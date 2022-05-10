package gologic

import (
	"fmt"
	"strings"
)

type Substitution struct {
	expressions []*Expr
	variables   []uint
}

func (s *Substitution) String() string {
	var builder strings.Builder
	builder.WriteString("{")
	if len(s.expressions) != 0 {
		builder.WriteString(s.expressions[0].String())
		builder.WriteString("/")
		builder.WriteString(fmt.Sprintf("x%d", s.variables[0]))
		for i, v := range s.expressions[1:] {
			builder.WriteString(", ")
			builder.WriteString(v.String())
			builder.WriteString("/")
			builder.WriteString(fmt.Sprintf("x%d", s.variables[i+1]))
		}
	}
	builder.WriteString("}")
	return builder.String()
}

func NewSubstitution(exprs []*Expr, vars []uint) *Substitution {
	if len(exprs) != len(vars) {
		panic("invalid argument lengths")
	}
	for i, v := range vars {
		for _, u := range vars[i+1:] {
			if v == u {
				panic("repeated variable")
			}
		}
	}
	return &Substitution{exprs, vars}
}

func (e *Expr) ApplySubstitution(s *Substitution) *Expr {
	if e == nil {
		return nil
	}
	switch e.class {
	case VariableClass:
		for i, v := range s.variables {
			if v == e.value {
				return s.expressions[i]
			}
		}
		return e
	case ConstantClass:
		return e
	case NotClass:
		return e.setLeft(e.left.ApplySubstitution(s))
	case ForallClass, ExistsClass:
		var vars []uint
		var exprs []*Expr
		for i, v := range s.variables {
			if e.value != v {
				vars = append(vars, v)
				exprs = append(exprs, s.expressions[i])
			}
		}
		return e.setLeft(e.left.ApplySubstitution(NewSubstitution(exprs, vars)))
	// case function, prop, comma, and, or, iff, then:
	default:
		return e.
			setLeft(e.left.ApplySubstitution(s)).
			setRight(e.right.ApplySubstitution(s))
	}
}

func (s *Substitution) Compose(other *Substitution) *Substitution {
	var vars []uint
	var exprs []*Expr
	for i, v := range s.variables {
		result := s.expressions[i].ApplySubstitution(other)
		if !result.Equal(Var(v)) {
			vars = append(vars, v)
			exprs = append(exprs, result)
		}
	}
	for i, v := range other.variables {
		var found bool
		for _, u := range s.variables {
			if v == u {
				found = true
				break
			}
		}
		if found {
			continue
		}
		vars = append(vars, v)
		exprs = append(exprs, other.expressions[i])
	}
	return NewSubstitution(exprs, vars)
}

func MGU(a, b *Expr) *Substitution {
	s1 := []*Expr{a}
	s2 := []*Expr{b}
	ret := NewSubstitution(nil, nil)
	for len(s1) != 0 {
		x := s1[len(s1)-1]
		y := s2[len(s2)-1]
		s1 = s1[:len(s1)-1]
		s2 = s2[:len(s2)-1]
		if _, ok := y.FreeVarsMap()[x.value]; x.class == VariableClass && !ok {
			sub := NewSubstitution([]*Expr{y}, []uint{x.value})
			ret = ret.Compose(sub)
			for i := range s1 {
				s1[i] = s1[i].ApplySubstitution(sub)
				s2[i] = s2[i].ApplySubstitution(sub)
			}
		} else if _, ok := x.FreeVarsMap()[y.value]; y.class == VariableClass && !ok {
			sub := NewSubstitution([]*Expr{x}, []uint{y.value})
			ret = ret.Compose(sub)
			for i := range s1 {
				s1[i] = s1[i].ApplySubstitution(sub)
				s2[i] = s2[i].ApplySubstitution(sub)
			}
		} else if x.class == y.class {
			if x.value == y.value && (x.class == PropClass || x.class == FunctionClass) {
				xArgs, yArgs := x.Children(), y.Children()
				if len(xArgs) != len(yArgs) {
					return nil
				}
				for i := range xArgs {
					s1 = append(s1, xArgs[i])
					s2 = append(s2, yArgs[i])
				}
			} else if x.class == NotClass {
				s1 = append(s1, x.left)
				s2 = append(s2, y.left)
			}
		} else if x.Equal(y) {
			continue
		} else {
			return nil
		}
	}
	return ret
}

func Resolve(c1, c2 []*Expr, i, j int) ([]*Expr, *Substitution) {
	var sub *Substitution
	if tmp := MGU(c1[i], Not(c2[j])); tmp != nil {
		sub = tmp
	} else if tmp := MGU(Not(c1[i]), c2[j]); tmp != nil {
		sub = tmp
	} else {
		return nil, nil
	}
	var ret []*Expr
	for inx, v := range c1 {
		if inx != i {
			ret = append(ret, v.ApplySubstitution(sub))
		}
	}
	for inx, v := range c2 {
		if inx != j {
			ret = append(ret, v.ApplySubstitution(sub))
		}
	}
	return ret, sub
}
