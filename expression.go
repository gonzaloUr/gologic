package gologic

import (
	"fmt"
	"sort"
)

const (
	VariableClass = iota
	ConstantClass
	FunctionClass
	PropClass
	comma
	NotClass
	ForallClass
	ExistsClass
	AndClass
	OrClass
	IffClass
	ThenClass
)

func IsTerm(class int) bool {
	return class == VariableClass || class == ConstantClass || class == FunctionClass
}

func IsForm(class int) bool {
	return !IsTerm(class) && class != comma
}

func IsQuantifier(class int) bool {
	return class == ExistsClass || class == ForallClass
}

func IsUnary(class int) bool {
	return class == NotClass || class == ExistsClass || class == ForallClass
}

func IsBinary(class int) bool {
	return class == AndClass || class == OrClass || class == IffClass || class == ThenClass
}

// A tree node that represents a first order logic formula.
type Expr struct {
	class int
	value uint
	left  *Expr
	right *Expr
	size  int
}

// Quantifier variable, function, constant or variable id.
func (e *Expr) Value() uint {
	return e.value
}

// Returns formula class.
func (e *Expr) Class() int {
	return e.class
}

// Returns all children of the given node.
func (e *Expr) Children() []*Expr {
	var ret []*Expr
	if e.left != nil {
		ret = append(ret, e.left)
	}
	if e.right != nil {
		curr := e.right
		for curr.class == comma {
			ret = append(ret, curr.left)
			curr = curr.right
		}
		ret = append(ret, curr)
	}
	return ret
}

// Helper constructor that auto calculates size field.
func newExpr(class int, value uint, left, right *Expr) *Expr {
	var size int
	if class == comma {
		size = 0
	} else {
		size = 1
	}
	if left != nil {
		size += left.size
	}
	if right != nil {
		size += right.size
	}
	return &Expr{
		class: class,
		value: value,
		left:  left,
		right: right,
		size:  size,
	}
}

// Returns s[0] □ (s[1] □ ... (s[n-1] □ s[n])...) where □ = class.
func sliceToTree(class int, s []*Expr) (*Expr, *Expr) {
	if len(s) == 0 {
		return nil, nil
	}
	if len(s) == 1 {
		return s[0], nil
	}
	left, right := s[0], s[len(s)-1]
	for i := len(s)-2; i >= 1; i-- {
		right = newExpr(class, 0, s[i], right)
	}
	return left, right
}

// Returns the nth variable xₙ.
func Var(n uint) *Expr {
	return newExpr(VariableClass, n, nil, nil)
}

// Creates the nth constant cₙ.
func Const(n uint) *Expr {
	return newExpr(ConstantClass, n, nil, nil)
}

// Creates a function term with symbol fₙ taking 1 or more term arguments.
func Func(n uint, args ...*Expr) *Expr {
	left, right := sliceToTree(comma, args)
	if left == nil && right == nil {
		panic("at least 1 argument expected")
	}
	return newExpr(FunctionClass, n, left, right)
}

// Creates a proposition with symbol Pₙ taking 0 or more term arguments.
func Prop(n uint, args ...*Expr) *Expr {
	left, right := sliceToTree(comma, args)
	return newExpr(PropClass, n, left, right)
}

func Unary(class int, value uint, e *Expr) *Expr {
	if !IsForm(e.class) {
		panic("form expected")
	}
	if !IsUnary(class) {
		panic("unary class expected")
	}
	return newExpr(class, value, e, nil)
}

// Given the formula e returns the formula ¬e.
func Not(e *Expr) *Expr {
	return Unary(NotClass, 0, e)
}

// Given the formula e returns the formula (∀ xₙ)e.
func Forall(n uint, e *Expr) *Expr {
	return Unary(ForallClass, n, e)
}

// Given the formula e returns the formula (∃ xₙ)e.
func Exists(n uint, e *Expr) *Expr {
	return Unary(ExistsClass, n, e)
}

func Binary(class int, e ...*Expr) *Expr {
	if !IsBinary(class) {
		panic("binary class expected")
	}
	left, right := sliceToTree(class, e)
	if left == nil || right == nil {
		panic("at least 2 arguments expected")
	}
	return newExpr(class, 0, left, right)
}

// Given the formulas e₁, e₂, ..., eₙ returns the formula e₁ ∧ e₂ ∧ ... ∧ eₙ
func And(e ...*Expr) *Expr {
	return Binary(AndClass, e...)
}

// Given the formulas e₁, e₂, ..., eₙ returns the formula e₁ ∨ e₂ ∨ ... ∨ eₙ
func Or(e ...*Expr) *Expr {
	return Binary(OrClass, e...)
}

// Given the formulas e₁, e₂, ..., eₙ returns the formula e₁ ⇔ (e₂ ⇔ ... (eₙ₋₁ ⇔ eₙ)...).
func Iff(e ...*Expr) *Expr {
	return Binary(IffClass, e...)
}

// Given the formulas e₁, e₂, ..., eₙ returns the formula e₁ ⇒ (e₂ ⇒ ... (eₙ₋₁ ⇒ eₙ)...).
func Then(e ...*Expr) *Expr {
	return Binary(ThenClass, e...)
}

func (e *Expr) setLeft(left *Expr) *Expr {
	if e.left == left {
		return e
	}
	return newExpr(e.class, e.value, left, e.right)
}

func (e *Expr) setRight(right *Expr) *Expr {
	if e.right == right {
		return e
	}
	return newExpr(e.class, e.value, e.left, right)
}

func (e *Expr) String() string {
	if e == nil {
		return ""
	}
	switch e.class {
	case VariableClass:
		return fmt.Sprintf("x%d", e.value)
	case ConstantClass:
		return fmt.Sprintf("c%d", e.value)
	case FunctionClass:
		if e.right == nil {
			return fmt.Sprintf("f%d(%v)", e.value, e.left)
		} else {
			return fmt.Sprintf("f%d(%v,%v)", e.value, e.left, e.right)
		}
	case PropClass:
		if e.left == nil && e.right == nil {
			return fmt.Sprintf("P%d", e.value)
		} else if e.right == nil {
			return fmt.Sprintf("P%d(%v)", e.value, e.left)
		} else {
			return fmt.Sprintf("P%d(%v,%v)", e.value, e.left, e.right)
		}
	case comma:
		return fmt.Sprintf("%v,%v", e.left, e.right)
	case NotClass:
		if IsUnary(e.left.class) || e.left.class == PropClass {
			return fmt.Sprintf("¬%v", e.left)
		}
		return fmt.Sprintf("¬(%v)", e.left)
	case ForallClass:
		if IsUnary(e.left.class) || e.left.class == PropClass {
			return fmt.Sprintf("∀x%d%v", e.value, e.left)
		}
		return fmt.Sprintf("∀x%d(%v)", e.value, e.left)
	case ExistsClass:
		if IsUnary(e.left.class) || e.left.class == PropClass {
			return fmt.Sprintf("∃x%d%v", e.value, e.left)
		}
		return fmt.Sprintf("∃x%d(%v)", e.value, e.left)
	case AndClass, OrClass:
		var left, right string
		if IsBinary(e.left.class) && e.left.class != e.class {
			left = fmt.Sprintf("(%v)", e.left)
		} else {
			left = fmt.Sprintf("%v", e.left)
		}
		if IsBinary(e.right.class) && e.right.class != e.class {
			right = fmt.Sprintf("(%v)", e.right)
		} else {
			right = fmt.Sprintf("%v", e.right)
		}
		if e.class == AndClass {
			return fmt.Sprintf("%s ∧ %s", left, right)
		} else {
			return fmt.Sprintf("%v ∨ %v", left, right)
		}
	// case IffClass, ThenClass:
	default:
		var left, right string
		if IsBinary(e.left.class) {
			left = fmt.Sprintf("(%v)", e.left)
		} else {
			left = fmt.Sprintf("%v", e.left)
		}
		if IsBinary(e.right.class) {
			right = fmt.Sprintf("(%v)", e.right)
		} else {
			right = fmt.Sprintf("%v", e.right)
		}
		switch e.class {
		case IffClass:
			return fmt.Sprintf("%v ⇔ %v", left, right)
		default:
			return fmt.Sprintf("%v ⇒ %v", left, right)
		}
	}
}

// Returns true iff e represents the same formula as other.
func (e *Expr) Equal(other *Expr) bool {
	if e == other {
		return true
	}
	if e == nil || other == nil {
		return false
	}
	return e.class == other.class &&
		e.value == other.value &&
		e.size == other.size &&
		e.left.Equal(other.left) &&
		e.right.Equal(other.right)
}

// Returns the substitution of every free ocurrence of Var(v) in e by s.
func (e *Expr) Substitute(s *Expr, v uint) *Expr {
	if e == nil {
		return nil
	}
	switch e.class {
	case VariableClass:
		if e.class == VariableClass && e.value == v {
			return s
		}
		return e
	case ConstantClass:
		return e
	case NotClass:
		return e.setLeft(e.left.Substitute(s, v))
	case ForallClass, ExistsClass:
		if e.value != v {
			return e.setLeft(e.left.Substitute(s, v))
		}
		return e
	// case function, prop, comma, and, or, iff, then:
	default:
		return e.setLeft(e.left.Substitute(s, v)).
			setRight(e.right.Substitute(s, v))
	}
}

func (e *Expr) RemoveIff() *Expr {
	if !IsForm(e.class) {
		panic("form expected")
	}
	switch e.class {
	case PropClass:
		return e
	case NotClass, ForallClass, ExistsClass:
		return e.setLeft(e.left.RemoveIff())
	case AndClass, OrClass, ThenClass:
		return e.setLeft(e.left.RemoveIff()).setRight(e.right.RemoveIff())
	// case iff:
	default:
		newLeft, newRight := e.left.RemoveIff(), e.right.RemoveIff()
		return And(Then(newLeft, newRight), Then(newRight, newLeft))
	}
}

func (e *Expr) RemoveThen() *Expr {
	if !IsForm(e.class) {
		panic("form expected")
	}
	switch e.class {
	case PropClass:
		return e
	case NotClass, ForallClass, ExistsClass:
		return e.setLeft(e.left.RemoveThen())
	case AndClass, OrClass, IffClass:
		return e.setLeft(e.left.RemoveThen()).setRight(e.right.RemoveThen())
	// case then:
	default:
		return Or(Not(e.left.RemoveThen()), e.right.RemoveThen())
	}
}

func (e *Expr) ReduceNot() *Expr {
	if !IsForm(e.class) {
		panic("form expected")
	}
	switch e.class {
	case PropClass:
		return e
	case ExistsClass, ForallClass:
		return e.setLeft(e.left.ReduceNot())
	case OrClass, AndClass, IffClass, ThenClass:
		return e.setLeft(e.left.ReduceNot()).setRight(e.right.ReduceNot())
	// case not:
	default:
		switch e.left.class {
		case NotClass:
			return e.left.left.ReduceNot()
		case AndClass:
			return Or(Not(e.left.left).ReduceNot(), Not(e.left.right).ReduceNot())
		case OrClass:
			return And(Not(e.left.left).ReduceNot(), Not(e.left.right).ReduceNot())
		case ForallClass:
			return Exists(e.left.value, Not(e.left.left).ReduceNot())
		case ExistsClass:
			return Forall(e.left.value, Not(e.left.left).ReduceNot())
		case ThenClass:
			return And(e.left.left, Not(e.left.right).ReduceNot())
		case IffClass:
			e1 := And(e.left.left, Not(e.left.right).ReduceNot())
			e2 := And(e.left.right, Not(e.left.left).ReduceNot())
			return Or(e1, e2)
		// case prop:
		default:
			return e
		}
	}
}

func (e *Expr) FreeVarsMap() map[uint]struct{} {
	if e == nil {
		return map[uint]struct{}{}
	}
	switch e.class {
	case VariableClass:
		return map[uint]struct{}{e.value: {}}
	case ConstantClass:
		return map[uint]struct{}{}
	case ForallClass, ExistsClass:
		s := e.left.FreeVarsMap()
		delete(s, e.value)
		return s
	default:
		s1, s2 := e.left.FreeVarsMap(), e.right.FreeVarsMap()
		for k, v := range s2 {
			s1[k] = v
		}
		return s1
	}
}

func (e *Expr) FreeVars() []uint {
	var vars []uint
	for v := range e.FreeVarsMap() {
		vars = append(vars, v)
	}
	sort.Slice(vars, func(i, j int) bool { return vars[i] < vars[j] })
	return vars
}

func (e *Expr) ReduceQuantifiers() *Expr {
	if !IsForm(e.class) {
		panic("form expected")
	}
	switch e.class {
	case PropClass:
		return e
	case ExistsClass, ForallClass:
		if _, ok := e.left.FreeVarsMap()[e.value]; ok {
			return e.setLeft(e.left.ReduceQuantifiers())
		}
		return e.left.ReduceQuantifiers()
	case NotClass:
		return e.setLeft(e.left.ReduceQuantifiers())
	// case and, or, then, iff:
	default:
		return e.
			setLeft(e.left.ReduceQuantifiers()).
			setRight(e.right.ReduceQuantifiers())
	}
}

func (e *Expr) UnusedVar() uint {
	if e == nil {
		return 0
	}
	switch e.class {
	case VariableClass:
		return e.value + 1
	case ConstantClass:
		return 0
	case NotClass:
		return e.left.UnusedVar()
	case ForallClass, ExistsClass:
		return max(e.value+1, e.left.UnusedVar())
	// case prop, comma, and, or, iff, then:
	default:
		return max(e.left.UnusedVar(), e.right.UnusedVar())
	}
}

func (e *Expr) UnusedConst() uint {
	if e == nil {
		return 0
	}
	switch e.class {
	case VariableClass:
		return 0
	case ConstantClass:
		return e.value + 1
	case NotClass, ForallClass, ExistsClass:
		return e.left.UnusedConst()
	// case prop, comma, and, or, iff, then:
	default:
		return max(e.left.UnusedConst(), e.right.UnusedConst())
	}
}

func (e *Expr) UnusedFunc() uint {
	if e == nil {
		return 0
	}
	switch e.class {
	case VariableClass, ConstantClass:
		return 0
	case FunctionClass:
		return max(e.left.UnusedFunc(), e.right.UnusedFunc(), e.value+1)
	case NotClass, ForallClass, ExistsClass:
		return e.left.UnusedFunc()
	// case prop, comma, and, or, iff, then:
	default:
		return max(e.left.UnusedFunc(), e.right.UnusedFunc())
	}
}

func (e *Expr) UnusedProp() uint {
	if !IsForm(e.class) {
		panic("form expected")
	}
	switch e.class {
	case PropClass:
		return e.value + 1
	case NotClass, ForallClass, ExistsClass:
		return e.left.UnusedProp()
	// case and, or, then, iff:
	default:
		return max(e.left.UnusedProp(), e.right.UnusedProp())
	}
}

func (e *Expr) Prenex() *Expr {
	if !IsForm(e.class) {
		panic("form expected")
	}
	if e.class == IffClass || e.class == ThenClass {
		panic("trying to prenex a formula with iff or then")
	}
	switch e.class {
	case PropClass:
		return e
	case NotClass, ForallClass, ExistsClass:
		return e.setLeft(e.left.Prenex())
	// case or, and:
	default:
		// e = e0 or e1.
		e0, e1 := e.left.Prenex(), e.right.Prenex()
		if IsQuantifier(e0.class) && IsQuantifier(e1.class) {
			z0 := e.UnusedVar()
			z1 := z0 + 1
			rhs := e0.left.Substitute(Var(z0), e0.value)
			lhs := e1.left.Substitute(Var(z1), e1.value)
			sub := Binary(e.class, rhs, lhs).Prenex()
			return Unary(e0.class, z0, Unary(e1.class, z1, sub))
		} else if !IsQuantifier(e0.class) && !IsQuantifier(e1.class) {
			return e.setLeft(e0).setRight(e1)
		} else if IsQuantifier(e0.class) {
			z := e.UnusedVar()
			sub := Binary(e.class, e0.left.Substitute(Var(z), e0.value), e1).Prenex()
			return Unary(e0.class, z, sub)
		} else {
			z := e.UnusedVar()
			sub := Binary(e.class, e0, e1.left.Substitute(Var(z), e1.value)).Prenex()
			return Unary(e1.class, z, sub)
		}
	}
}

type SkolemAxiom struct {
	// Skolem function or constant.
	Term *Expr

	// Corresponding exists formula for the skolem function or constant.
	Form *Expr
}

func (s *SkolemAxiom) String() string {
	return fmt.Sprintf("[%v, %v]", s.Term, s.Form)
}

// A collection of function and constant symbols part of a first order language.
type Symbols struct {
	Constants []uint
	Functions []uint
}

func (s *Symbols) UnusedConst() uint {
	ret := uint(0)
	for _, v := range s.Constants {
		ret = max(ret, v+1)
	}
	return ret
}

func (s *Symbols) UnusedFunc() uint {
	ret := uint(0)
	for _, v := range s.Functions {
		ret = max(ret, v+1)
	}
	return ret
}

func (e *Expr) skolemizeHelper(s *Symbols, varsAc []*Expr) (*Expr, []*SkolemAxiom) {
	switch e.class {
	case ExistsClass:
		var skolemExpr *Expr
		if len(varsAc) == 0 {
			skolemExpr = Const(max(e.UnusedConst(), s.UnusedConst()))
		} else {
			skolemExpr = Func(max(e.UnusedFunc(), s.UnusedFunc()), varsAc...)
		}
		sub := e.left.Substitute(skolemExpr, e.value)
		ret, defs := sub.skolemizeHelper(s, varsAc)
		if e.left.Equal(sub) {
			return ret, defs
		}
		defs = append(defs, &SkolemAxiom{skolemExpr, e})
		return ret, defs
	case ForallClass:
		sub, defs := e.left.skolemizeHelper(s, append(varsAc, Var(e.value)))
		return e.setLeft(sub), defs
	default:
		return e, []*SkolemAxiom{}
	}
}

// Skolemizes a form considering the passed symbols part of the language.
func (e *Expr) SkolemizeWith(symbols *Symbols) (*Expr, []*SkolemAxiom) {
	if !IsForm(e.class) {
		panic("form expected")
	}
	r, defs := e.skolemizeHelper(symbols, []*Expr{})
	for i := 0; i < len(defs) / 2; i++ {
		tmp := defs[i]
		defs[i] = defs[len(defs)-(i+1)]
		defs[len(defs)-(i+1)] = tmp
	}
	return r, defs
}

func (e *Expr) Skolemize() (*Expr, []*SkolemAxiom) {
	return e.SkolemizeWith(&Symbols{})
}

func (e *Expr) Matrix() *Expr {
	if !IsForm(e.class) {
		panic("form expected")
	}
	for IsQuantifier(e.class) {
		e = e.left
	}
	return e
}

func (e *Expr) CNF() *Expr {
	switch e.class {
	case PropClass, NotClass:
		return e
	case AndClass:
		return e.setLeft(e.left.CNF()).setRight(e.right.CNF())
	case OrClass:
		e0, e1 := e.left.CNF(), e.right.CNF()
		if e0.class == AndClass {
			return And(Or(e0.left, e1).CNF(), Or(e1, e0.right).CNF())
		} else if e1.class == AndClass {
			return And(Or(e0, e1.left).CNF(), Or(e0, e1.right).CNF())
		} else {
			return e.setLeft(e0).setLeft(e1)
		}
	default:
		panic("found invalid connective")
	}
}

func (e *Expr) Closure() *Expr {
	if !IsForm(e.class) {
		panic("form expected")
	}
	ret := e
	for _, variable := range e.FreeVars() {
		ret = Forall(variable, ret)
	}
	return ret
}
