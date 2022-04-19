package gologic

import "fmt"

const (
	variable int = iota
	constant
	function
	prop
	comma
	not
	forall
	exists
	and
	or
	iff
	then
)

// Represents a first order logic formula or term as a binary tree.
type Expr struct {
	class int
	value uint
	left  *Expr
	right *Expr
	size  int
}

// Helper constructor that auto calculates size field.
func newExpr(class int, value uint, left, right *Expr) *Expr {
	size := 1
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

type UpdateExpr struct {
	Expr
	original     *Expr
	updatedClass bool
	updatedValue bool
	updatedLeft  bool
	updatedRight bool
}

func (u *UpdateExpr) SetClass(class int) *UpdateExpr {
	u.updatedClass = true
	u.class = class
	return u
}

func (u *UpdateExpr) SetValue(value uint) *UpdateExpr {
	u.updatedValue = true
	u.value = value
	return u
}

func (u *UpdateExpr) SetLeft(left *Expr) *UpdateExpr {
	u.updatedLeft = true
	u.left = left
	return u
}

func (u *UpdateExpr) SetRight(right *Expr) *UpdateExpr {
	u.updatedRight = true
	u.right = right
	return u
}

func (e *Expr) SetClass(class int) *UpdateExpr {
	return (&UpdateExpr{original: e}).SetClass(class)
}

func (e *Expr) SetValue(value uint) *UpdateExpr {
	return (&UpdateExpr{original: e}).SetValue(value)
}

func (e *Expr) SetLeft(left *Expr) *UpdateExpr {
	return (&UpdateExpr{original: e}).SetLeft(left)
}

func (e *Expr) SetRight(right *Expr) *UpdateExpr {
	return (&UpdateExpr{original: e}).SetRight(right)
}

func (u *UpdateExpr) Build() *Expr {
	class := u.original.class
	value := u.original.value
	left := u.original.left
	right := u.original.right
	if u.updatedClass {
		class = u.class
	}
	if u.updatedValue {
		value = u.value
	}
	if u.updatedLeft {
		left = u.left
	}
	if u.updatedRight {
		right = u.right
	}
	changed := class != u.original.class ||
		value != u.original.value ||
		left != u.original.left ||
		right != u.original.right
	if changed {
		return newExpr(class, value, left, right)
	}
	return u.original
}

// Returns the nth variable xₙ.
func Var(n uint) *Expr {
	return newExpr(variable, n, nil, nil)
}

// Creates the nth constant cₙ.
func Const(n uint) *Expr {
	return newExpr(constant, n, nil, nil)
}

func isTerm(class int) bool {
	return class == variable || class == constant || class == function
}

func assertNonNil(e *Expr) {
	if e == nil {
		panic("non nil expression expected")
	}
}

func assertTerm(e *Expr) {
	assertNonNil(e)
	if !isTerm(e.class) {
		panic("term expression expected")
	}
}

func assertForm(e *Expr) {
	assertNonNil(e)
	if isTerm(e.class) {
		panic("form expression expected")
	}
}

// Helper function for Func and Prop constructors.
func funcPropHelper(n uint, args []*Expr, class int, noArgs func() *Expr) *Expr {
	if len(args) == 0 {
		return noArgs()
	}
	if len(args) == 1 {
		assertTerm(args[0])
		return newExpr(class, n, args[0], nil)
	}
	if len(args) == 2 {
		assertTerm(args[0])
		assertTerm(args[1])
		return newExpr(class, n, args[0], args[1])
	}
	assertTerm(args[len(args)-1])
	assertTerm(args[len(args)-2])
	cur := newExpr(comma, 0, args[len(args)-1], args[len(args)-2])
	for i := len(args) - 3; i > 0; i-- {
		assertTerm(args[i])
		cur = newExpr(comma, 0, args[i], cur)
	}
	assertTerm(args[0])
	return newExpr(class, n, args[0], cur)
}

// Creates a function term with symbol fₙ taking 1 or more term arguments.
func Func(n uint, args ...*Expr) *Expr {
	return funcPropHelper(n, args, function, func() *Expr {
		panic("at least 1 argument expected")
	})
}

// Creates a proposition with symbol Pₙ taking 0 or more term arguments.
func Prop(n uint, args ...*Expr) *Expr {
	return funcPropHelper(n, args, prop, func() *Expr {
		return newExpr(prop, n, nil, nil)
	})
}

// Helper function for unary connective constructors (not, forall, exists).
func unaryHelper(class int, value uint, e *Expr) *Expr {
	assertForm(e)
	return newExpr(class, value, e, nil)
}

// Given the formula e returns the formula ¬e.
func Not(e *Expr) *Expr {
	return unaryHelper(not, 0, e)
}

// Given the formula e returns the formula (∀ xₙ)e.
func Forall(n uint, e *Expr) *Expr {
	return unaryHelper(forall, n, e)
}

// Given the formula e returns the formula (∃ xₙ)e.
func Exists(n uint, e *Expr) *Expr {
	return unaryHelper(exists, n, e)
}

// Helper function for binary connective constructors (and, or, then, iff).
func binaryHelper(class int, e ...*Expr) *Expr {
	if len(e) < 2 {
		panic("at least 2 arguments expected")
	}
	assertForm(e[len(e)-1])
	assertForm(e[len(e)-2])
	curr := newExpr(class, 0, e[len(e)-1], e[len(e)-2])
	for i := len(e) - 3; i >= 0; i-- {
		assertForm(e[i])
		curr = newExpr(class, 0, curr, e[i])
	}
	return curr
}

// Given the formulas e₁, e₂, ..., eₙ returns the formula e₁ ∧ e₂ ∧ ... ∧ eₙ
func And(e ...*Expr) *Expr {
	return binaryHelper(and, e...)
}

// Given the formulas e₁, e₂, ..., eₙ returns the formula e₁ ∨ e₂ ∨ ... ∨ eₙ
func Or(e ...*Expr) *Expr {
	return binaryHelper(or, e...)
}

// Given the formulas e₁, e₂, ..., eₙ returns the formula e₁ ⇔ (e₂ ⇔ (e₃ ⇔ ... (eₙ₋₁ ⇔ eₙ)...)).
func Iff(e ...*Expr) *Expr {
	return binaryHelper(iff, e...)
}

// Given the formulas e₁, e₂, ..., eₙ returns the formula e₁ ⇒ (e₂ ⇒ (e₃ ⇒ ... (eₙ₋₁ ⇒ eₙ)...)).
func Then(e ...*Expr) *Expr {
	return binaryHelper(then, e...)
}

func (e *Expr) String() string {
	if e == nil {
		return ""
	}
	switch e.class {
	case variable:
		return fmt.Sprintf("x%d", e.value)
	case constant:
		return fmt.Sprintf("c%d", e.value)
	case function:
		if e.right == nil {
			return fmt.Sprintf("f%d(%v)", e.value, e.left)
		} else {
			return fmt.Sprintf("f%d(%v,%v)", e.value, e.left, e.right)
		}
	case prop:
		if e.left == nil && e.right == nil {
			return fmt.Sprintf("P%d", e.value)
		} else if e.left != nil {
			return fmt.Sprintf("P%d(%v)", e.value, e.left)
		} else {
			return fmt.Sprintf("P%d(%v,%v)", e.value, e.left, e.right)
		}
	case comma:
		return fmt.Sprintf("%v,%v", e.left, e.right)
	case not:
		return fmt.Sprintf("¬%v", e.left)
	case forall:
		return fmt.Sprintf("∀x%d(%v)", e.value, e.left)
	case exists:
		return fmt.Sprintf("∃x%d(%v)", e.value, e.left)
	case and:
		return fmt.Sprintf("(%v ∧ %v)", e.left, e.right)
	case or:
		return fmt.Sprintf("(%v ∨ %v)", e.left, e.right)
	case iff:
		return fmt.Sprintf("(%v ⇔ %v)", e.left, e.right)
	// case then:
	default:
		return fmt.Sprintf("(%v ⇒ %v)", e.left, e.right)
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
	case variable:
		if e.class == variable && e.value == v {
			return s
		}
		return e
	case constant:
		return e
	case not, forall, exists:
		return e.SetLeft(e.left.Substitute(s, v)).Build()
	// case function, prop, comma, and, or, iff, then:
	default:
		return e.SetLeft(e.left.Substitute(s, v)).
			SetRight(e.right.Substitute(s, v)).
			Build()
	}
}

func (e *Expr) RemoveIff() *Expr {
	assertForm(e)
	switch e.class {
	case prop:
		return e
	case not, forall, exists:
		return e.SetLeft(e.left.RemoveIff()).Build()
	case and, or, then:
		return e.SetLeft(e.left.RemoveIff()).SetRight(e.right.RemoveIff()).Build()
	// case iff:
	default:
		newLeft, newRight := e.left.RemoveIff(), e.right.RemoveIff()
		return And(Then(newLeft, newRight), Then(newRight, newLeft))
	}
}

func (e *Expr) RemoveThen() *Expr {
	assertForm(e)
	switch e.class {
	case prop:
		return e
	case not, forall, exists:
		return e.SetLeft(e.left.RemoveThen()).Build()
	case and, or, iff:
		return e.SetLeft(e.left.RemoveThen()).SetRight(e.right.RemoveThen()).Build()
	// case then:
	default:
		return Or(Not(e.left.RemoveThen()), e.right.RemoveThen())
	}
}

func (e *Expr) ReduceNot() *Expr {
	assertForm(e)
	switch e.class {
	case prop:
		return e
	case exists, forall:
		return e.SetLeft(e.left.ReduceNot()).Build()
	case or, and, iff, then:
		return e.SetLeft(e.left.ReduceNot()).SetRight(e.right.ReduceNot()).Build()
	// case not:
	default:
		switch e.left.class {
		case not:
			return e.left.left.ReduceNot()
		case and:
			return Or(Not(e.left.left).ReduceNot(), Not(e.left.right).ReduceNot())
		case or:
			return And(Not(e.left.left).ReduceNot(), Not(e.left.right).ReduceNot())
		case forall:
			return Exists(e.left.value, Not(e.left.left).ReduceNot())
		case exists:
			return Forall(e.left.value, Not(e.left.left).ReduceNot())
		case then:
			return And(e.left.left, Not(e.left.right).ReduceNot())
		case iff:
			e1 := And(e.left.left, Not(e.left.right).ReduceNot())
			e2 := And(e.left.right, Not(e.left.left).ReduceNot())
			return Or(e1, e2)
		// case prop:
		default:
			return e
		}
	}
}

func (e *Expr) UnusedVar() uint {
	if e == nil {
		return 0
	}
	switch e.class {
	case variable:
		return e.value + 1
	case constant:
		return 0
	case not:
		return e.left.UnusedVar()
	case forall, exists:
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
	case variable:
		return 0
	case constant:
		return e.value + 1
	case not, forall, exists:
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
	case variable, constant:
		return 0
	case function:
		return e.value + 1
	case not, forall, exists:
		return e.left.UnusedFunc()
	// case prop, comma, and, or, iff, then:
	default:
		return max(e.left.UnusedFunc(), e.right.UnusedFunc())
	}
}

func (e *Expr) UnusedProp() uint {
	assertForm(e)
	switch e.class {
	case prop:
		return e.value + 1
	case not, forall, exists:
		return e.left.UnusedProp()
	// case and, or, then, iff:
	default:
		return max(e.left.UnusedProp(), e.right.UnusedProp())
	}
}

func isQuantifier(class int) bool {
	return class == exists || class == forall
}

func (e *Expr) Prenex() *Expr {
	assertForm(e)
	if e.class == iff || e.class == then {
		panic("trying to prenex a formula with iff or then")
	}
	switch e.class {
	case prop:
		return e
	case not, forall, exists:
		return e.SetLeft(e.left.Prenex()).Build()
	// case or, and:
	default:
		e0, e1 := e.left.Prenex(), e.right.Prenex()
		if isQuantifier(e0.class) && isQuantifier(e1.class) {
			z_0 := e.UnusedVar()
			z_1 := z_0 + 1
			rhs := e0.left.Substitute(Var(z_0), e0.value)
			lhs := e1.left.Substitute(Var(z_1), e1.value)
			sub := binaryHelper(e.class, rhs, lhs).Prenex()
			return unaryHelper(e0.class, z_0, unaryHelper(e1.class, z_1, sub))
		} else if !isQuantifier(e0.class) && !isQuantifier(e1.class) {
			return e.SetLeft(e0).SetRight(e1).Build()
		} else if isQuantifier(e0.class) {
			z := e.UnusedVar()
			sub := binaryHelper(e.class, e0.left.Substitute(Var(z), e0.value), e1).Prenex()
			return unaryHelper(e0.class, z, sub)
		} else {
			z := e.UnusedVar()
			sub := binaryHelper(e.class, e0, e1.left.Substitute(Var(z), e1.value)).Prenex()
			return unaryHelper(e0.class, z, sub)
		}
	}
}

func (e *Expr) skolemizeHelper(varsAc []*Expr) *Expr {
	switch e.class {
	case exists:
		sub := e.left.skolemizeHelper(varsAc)
		if len(varsAc) == 0 {
			constantId := sub.UnusedConst()
			return sub.Substitute(Const(constantId), e.value)
		} else {
			functionId := sub.UnusedFunc()
			return sub.Substitute(Func(functionId, varsAc...), e.value)
		}
	case forall:
		return e.SetLeft(e.left.skolemizeHelper(append(varsAc, Var(e.value)))).Build()
	default:
		return e
	}
}

func (e *Expr) Skolemize() *Expr {
	assertForm(e)
	return e.skolemizeHelper([]*Expr{})
}

func (e *Expr) Matrix() *Expr {
	assertForm(e)
	for isQuantifier(e.class) {
		e = e.left
	}
	return e
}

func (e *Expr) CNF() *Expr {
	switch e.class {
	case prop, not:
		return e
	case and:
		return e.SetLeft(e.left.CNF()).SetRight(e.right.CNF()).Build()
	case or:
		e0, e1 := e.left.CNF(), e.right.CNF()
		if e0.class == and {
			return And(Or(e0.left, e1).CNF(), Or(e1, e0.right).CNF())
		} else if e1.class == and {
			return And(Or(e0, e1.left).CNF(), Or(e0, e1.right).CNF())
		} else {
			return e.SetLeft(e0).SetLeft(e1).Build()
		}
	default:
		panic("found invalid connective")
	}
}

func (e *Expr) FreeVars() map[uint]struct{} {
	if e == nil {
		return map[uint]struct{}{}
	}
	switch e.class {
	case variable:
		return map[uint]struct{}{e.value: {}}
	case constant:
		return map[uint]struct{}{}
	case forall, exists:
		s := e.left.FreeVars()
		delete(s, e.value)
		return s
	default:
		s1, s2 := e.left.FreeVars(), e.right.FreeVars()
		for k, v := range s2 {
			s1[k] = v
		}
		return s1
	}
}

func (e *Expr) Closure() *Expr {
	assertForm(e)
	ret := e
	for variable := range e.FreeVars() {
		ret = Forall(variable, ret)
	}
	return ret
}

type Model[T comparable] struct {
	Constants    map[uint]T
	Functions    map[uint]func([]T) T
	Propositions map[uint]func([]T) bool
}

func (m *Model[T]) evalTermHelper(e *Expr) []T {
	if e == nil {
		return []T{}
	}
	switch e.class {
	case variable:
		panic("trying to evaluate a variable!")
	case constant:
		return []T{m.Constants[e.value]}
	case comma:
		return append(m.evalTermHelper(e.left), m.evalTermHelper(e.right)...)
	// case function:
	default:
		args := m.evalTermHelper(e.left)
		if e.right != nil {
			args = append(args, m.evalTermHelper(e.right)...)
		}
		return []T{m.Functions[e.value](args)}
	}
}

func (m *Model[T]) EvalTerm(e *Expr) T {
	assertTerm(e)
	return m.evalTermHelper(e)[0]
}

func (m *Model[T]) EvalForm(e *Expr) bool {
	assertForm(e)
	getConstants := func() []uint {
		constants := make([]uint, len(m.Constants))
		i := 0
		for k := range m.Constants {
			constants[i] = k
		}
		return constants
	}
	switch e.class {
	case prop:
		return m.Propositions[e.value](append(m.evalTermHelper(e.left), m.evalTermHelper(e.right)...))
	case not:
		return !m.EvalForm(e.left)
	case forall:
		for _, c := range getConstants() {
			if !m.EvalForm(e.left.Substitute(Const(c), e.value)) {
				return false
			}
		}
		return true
	case exists:
		for _, c := range getConstants() {
			if m.EvalForm(e.left.Substitute(Const(c), e.value)) {
				return true
			}
		}
		return false
	case and:
		return m.EvalForm(e.left) && m.EvalForm(e.right)
	case or:
		return m.EvalForm(e.left) || m.EvalForm(e.right)
	case iff:
		return m.EvalForm(e.left) == m.EvalForm(e.right)
	// case then:
	default:
		return !m.EvalForm(e.left) || m.EvalForm(e.right)
	}
}
