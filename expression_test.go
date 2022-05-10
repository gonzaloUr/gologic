package gologic

import (
	"math/rand"
	"reflect"
	"testing"
	"testing/quick"
)

const (
	MaxArgsFunc = 3
	MaxArgsProp = 3
	MaxIdFunc   = 5
	MaxIdProp   = 5
	MaxIdConst  = 5
	MaxIdVar    = 20
)

func pow(b, n int) int {
	ret := 1
	for i := 0; i < n; i++ {
		ret *= b
	}
	return ret
}

type BitArray []bool

func (b BitArray) Equal(other BitArray) bool {
	if len(b) != len(other) {
		return false
	}
	for i := range b {
		if b[i] != other[i] {
			return false
		}
	}
	return true
}

// Model over boolean values with at least two constants for true and false.
type Model struct {
	// True constant id.
	TrueConst uint

	// False constant id.
	FalseConst uint

	// Set of true constants.
	Constants map[uint]struct{}

	// Map from function id and args length to a set of true assigments.
	Functions map[uint]map[int][]BitArray

	// Map from prop id and args length to a set of true assigments.
	Propositions map[uint]map[int][]BitArray
}

func (m *Model) EvalTerm(e *Expr) []bool {
	if e == nil {
		return []bool{}
	}
	switch e.class {
	case ConstantClass:
		if _, ok := m.Constants[e.value]; ok {
			return []bool{true}
		}
		return []bool{false}
	case comma:
		return append(m.EvalTerm(e.left), m.EvalTerm(e.right)...)
	case FunctionClass:
		args := append(m.EvalTerm(e.left), m.EvalTerm(e.right)...)
		for _, array := range m.Functions[e.value][len(args)] {
			if array.Equal(args) {
				return []bool{true}
			}
		}
		return []bool{false}
	default:
		panic("invalid expression class")
	}
}

func (m *Model) EvalForm(e *Expr) bool {
	switch e.class {
	case PropClass:
		args := append(m.EvalTerm(e.left), m.EvalTerm(e.right)...)
		for _, array := range m.Functions[e.value][len(args)] {
			if array.Equal(args) {
				return true
			}
		}
		return false
	case AndClass:
		return m.EvalForm(e.left) && m.EvalForm(e.right)
	case OrClass:
		return m.EvalForm(e.left) || m.EvalForm(e.right)
	case IffClass:
		return m.EvalForm(e.left) == m.EvalForm(e.right)
	case ThenClass:
		return !m.EvalForm(e.left) || m.EvalForm(e.right)
	case NotClass:
		return !m.EvalForm(e.left)
	case ForallClass:
		for _, id := range []uint{m.TrueConst, m.FalseConst} {
			if !m.EvalForm(e.left.Substitute(Const(uint(id)), e.value)) {
				return false
			}
		}
		return true
	case ExistsClass:
		for _, id := range []uint{m.TrueConst, m.FalseConst} {
			if m.EvalForm(e.left.Substitute(Const(uint(id)), e.value)) {
				return true
			}
		}
		return false
	default:
		panic("invalid expression class")
	}
}

func RepeatingPermutation[T comparable](length int, elems []T) [][]T {
	ret := make([][]T, pow(len(elems), length))
	for i := range ret {
		ret[i] = make([]T, length)
	}
	for permElemInx := 0; permElemInx < length; permElemInx++ {
		eachElemAmount := pow(len(elems), permElemInx)
		permIndex := 0
		for permIndex < len(ret) {
			for currElem := 0; currElem < len(elems) && permIndex < len(ret); currElem++ {
				for i := 0; i < eachElemAmount && permIndex < len(ret); i++ {
					ret[permIndex][permElemInx] = elems[currElem]
					permIndex++
				}
			}
		}
	}
	return ret
}

// Returns all the assignments of free vars found in e such that e is true.
func (m *Model) TrueAssigments(e *Expr) []map[uint]bool {
	var ret []map[uint]bool
	freeVars := e.FreeVars()
	trueConst := Const(m.TrueConst)
	falseConst := Const(m.FalseConst)
	assigments := RepeatingPermutation(len(freeVars), []*Expr{trueConst, falseConst})
	for _, assigment := range assigments {
		subResult := e
		for i := range freeVars {
			subResult = subResult.Substitute(assigment[i], freeVars[i])
		}
		if m.EvalForm(subResult) {
			entry := make(map[uint]bool, len(freeVars))
			for i := range freeVars {
				if assigment[i].Equal(trueConst) {
					entry[freeVars[i]] = true
				} else {
					entry[freeVars[i]] = false
				}
			}
			ret = append(ret, entry)
		}
	}
	return ret
}

// Returns function arguments in order of appearance.
func (e *Expr) Args() []*Expr {
	if e == nil {
		return []*Expr{}
	}
	switch e.class {
	case FunctionClass, comma:
		return append(e.left.Args(), e.right.Args()...)
	default:
		return []*Expr{e}
	}
}

// Extends the model such that it verifies the given skolem axioms.
func (m *Model) ExtendModel(axioms []*SkolemAxiom) {
	for _, axiom := range axioms {
		assigments := m.TrueAssigments(axiom.Form.left)
		if axiom.Term.class == ConstantClass {
			if len(assigments) != 0 {
				var value bool
				for _, assigment := range assigments {
					for _, v := range assigment {
						value = v
						break
					}
					break
				}
				if value {
					m.Constants[axiom.Term.value] = struct{}{}
				}
			}
		} else {
			resultVar := axiom.Form.value
			argVars := axiom.Term.Args()
			var funcDefinition []BitArray
			for _, assigment := range assigments {
				if !assigment[resultVar] {
					continue
				}
				bits := make(BitArray, 0, len(argVars)-1)
				for _, arg := range argVars {
					if assigment[arg.value] {
						bits = append(bits, true)
					} else {
						bits = append(bits, false)
					}
				}
				funcDefinition = append(funcDefinition, bits)
			}
			if m.Functions[axiom.Term.value] == nil {
				m.Functions[axiom.Term.value] = map[int][]BitArray{}
			}
			m.Functions[axiom.Term.value][len(argVars)] = funcDefinition
		}
	}
}

func GenerateModel(rand *rand.Rand) *Model {
	constants := make(map[uint]struct{}, MaxIdConst+3)
	trueConst, falseConst := ^uint(0), ^uint(0)-1
	constants[trueConst] = struct{}{}
	for i := uint(0); i <= MaxIdConst; i++ {
		if rand.Intn(2) == 0 {
			constants[i] = struct{}{}
		}
	}
	functions := make(map[uint]map[int][]BitArray, MaxIdFunc+1)
	for i := uint(0); i <= MaxIdFunc; i++ {
		functions[i] = make(map[int][]BitArray, MaxArgsFunc)
		for length := 1; length <= MaxArgsFunc; length++ {
			for _, perm := range RepeatingPermutation(length, []bool{true, false}) {
				if rand.Intn(2) == 0 {
					functions[i][length] = append(functions[i][length], perm)
				}
			}
		}
	}
	propositions := make(map[uint]map[int][]BitArray, MaxIdProp+1)
	for i := uint(0); i <= MaxIdProp; i++ {
		propositions[i] = make(map[int][]BitArray, MaxArgsProp+1)
		if rand.Intn(2) == 0 {
			propositions[i][0] = []BitArray{{}}
		}
		for length := 1; length <= MaxArgsProp; length++ {
			for _, perm := range RepeatingPermutation(length, []bool{true, false}) {
				if rand.Intn(2) == 0 {
					propositions[i][length] = append(propositions[i][length], perm)
				}
			}
		}
	}
	return &Model{
		TrueConst:    trueConst,
		FalseConst:   falseConst,
		Constants:    constants,
		Functions:    functions,
		Propositions: propositions,
	}
}

// Returns a random slice of positive non zero ints that sum up to result and len between [min, max].
func IntSum(rand *rand.Rand, min, max, result int) []int {
	// Create random array of 1s from [1,result].
	ret := make([]int, rand.Intn(max)+min)
	for i := range ret {
		ret[i] = 1
	}
	// Randonly assign the remaining result-sum(ret) units to the elements of ret.
	for i := len(ret) + 1; i <= result; i++ {
		ret[rand.Intn(len(ret))]++
	}
	return ret
}

func GenerateTerm(rand *rand.Rand, size int) *Expr {
	if size == 1 {
		if rand.Intn(2) == 0 {
			return Const(uint(rand.Intn(MaxIdConst)))
		} else {
			return Var(uint(rand.Intn(MaxIdVar)))
		}
	} else {
		return Func(uint(rand.Intn(MaxIdFunc)), GenerateTerms(rand, size-1)...)
	}
}

func GenerateTerms(rand *rand.Rand, size int) []*Expr {
	sizes := IntSum(rand, 1, min(MaxArgsFunc, size), size)
	args := make([]*Expr, len(sizes))
	for i, v := range sizes {
		args[i] = GenerateTerm(rand, v)
	}
	return args
}

func min[T Number](args ...T) T {
	var ret = args[0]
	for _, v := range args[1:] {
		if v < ret {
			ret = v
		}
	}
	return ret
}

func GenerateForm(rand *rand.Rand, size int) *Expr {
	generateForms := func(size int) (*Expr, *Expr) {
		fstArgSize := rand.Intn(size-1) + 1
		sndArgSize := size - fstArgSize
		return GenerateForm(rand, fstArgSize), GenerateForm(rand, sndArgSize)
	}
	if size == 1 {
		return Prop(uint(rand.Intn(MaxIdProp)))
	}
	var choice int
	if size == 2 {
		choice = rand.Intn(4)
	} else {
		choice = rand.Intn(8)
	}
	switch choice {
	case 0:
		return Prop(uint(rand.Intn(MaxIdProp)), GenerateTerms(rand, size-1)...)
	case 1:
		return Not(GenerateForm(rand, size-1))
	case 2:
		return Forall(uint(rand.Intn(MaxIdVar)), GenerateForm(rand, size-1))
	case 3:
		return Exists(uint(rand.Intn(MaxIdVar)), GenerateForm(rand, size-1))
	case 4:
		return And(generateForms(size - 1))
	case 5:
		return Or(generateForms(size - 1))
	case 6:
		return Iff(generateForms(size - 1))
	default:
		return Then(generateForms(size - 1))
	}
}

func TestRemoveThen(t *testing.T) {
	equiv := func(e *Expr, m *Model) bool {
		e = e.Closure()
		return m.EvalForm(e) == m.EvalForm(e.RemoveThen())
	}
	if err := quick.Check(equiv, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
			v[1] = reflect.ValueOf(GenerateModel(r))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestRemoveIff(t *testing.T) {
	equiv := func(e *Expr, m *Model) bool {
		e = e.Closure()
		return m.EvalForm(e) == m.EvalForm(e.RemoveIff())
	}
	if err := quick.Check(equiv, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
			v[1] = reflect.ValueOf(GenerateModel(r))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestReduceNot(t *testing.T) {
	equiv := func(e *Expr, m *Model) bool {
		e = e.Closure()
		return m.EvalForm(e) == m.EvalForm(e.ReduceNot())
	}
	if err := quick.Check(equiv, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
			v[1] = reflect.ValueOf(GenerateModel(r))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestPrenex(t *testing.T) {
	equiv := func(e *Expr, m *Model) bool {
		e = e.Closure()
		return m.EvalForm(e) == m.EvalForm(e.RemoveIff().RemoveThen().ReduceNot().Prenex())
	}
	if err := quick.Check(equiv, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
			v[1] = reflect.ValueOf(GenerateModel(r))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestClosure(t *testing.T) {
	equiv := func(e *Expr) bool {
		return len(e.Closure().FreeVars()) == 0
	}
	if err := quick.Check(equiv, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
		},
	}); err != nil {
		t.Error(err)
	}
}

func nodeNotFound(class int, value uint, e *Expr) bool {
	stack := make([]*Expr, 1, e.size)
	stack[0] = e
	for len(stack) != 0 {
		top := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if top.class == class && top.value == value {
			return false
		}
		if top.left != nil {
			stack = append(stack, top.left)
		}
		if top.right != nil {
			stack = append(stack, top.right)
		}
	}
	return true
}

func TestUnusedConst(t *testing.T) {
	prop := func(e *Expr) bool {
		ret := e.UnusedConst()
		return nodeNotFound(ConstantClass, ret, e)
	}
	if err := quick.Check(prop, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestUnusedVar(t *testing.T) {
	prop := func(e *Expr) bool {
		ret := e.UnusedVar()
		return nodeNotFound(VariableClass, ret, e)
	}
	if err := quick.Check(prop, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestUnusedFunc(t *testing.T) {
	prop := func(e *Expr) bool {
		ret := e.UnusedFunc()
		return nodeNotFound(FunctionClass, ret, e)
	}
	if err := quick.Check(prop, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestUnusedProp(t *testing.T) {
	prop := func(e *Expr) bool {
		ret := e.UnusedProp()
		return nodeNotFound(PropClass, ret, e)
	}
	if err := quick.Check(prop, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestSkolemize(t *testing.T) {
	usedConstIds := make([]uint, MaxIdConst+1)
	for i := 0; i <= MaxIdConst; i++ {
		usedConstIds[i] = uint(i)
	}
	usedFuncIds := make([]uint, MaxIdFunc+1)
	for i := 0; i <= MaxIdFunc; i++ {
		usedFuncIds[i] = uint(i)
	}
	symbols := &Symbols{
		Constants: usedConstIds,
		Functions: usedConstIds,
	}
	prop := func(e *Expr, m *Model) bool {
		e = e.Closure().RemoveIff().RemoveThen().ReduceNot().Prenex().ReduceQuantifiers()
		ret, axioms := e.SkolemizeWith(symbols)
		m.ExtendModel(axioms)
		return m.EvalForm(ret) == m.EvalForm(e)
	}
	if err := quick.Check(prop, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			v[0] = reflect.ValueOf(GenerateForm(r, 15))
			v[1] = reflect.ValueOf(GenerateModel(r))
		},
	}); err != nil {
		t.Error(err)
	}
}

func TestChildren(t *testing.T) {
	prop := func(args []*Expr) bool {
		expr := Func(0, args...)
		ret := expr.Children()
		if len(ret) != len(args) {
			return false
		}
		for i := range ret {
			if !ret[i].Equal(args[i]) {
				return false
			}
		}
		return true
	}
	if err := quick.Check(prop, &quick.Config{
		Values: func(v []reflect.Value, r *rand.Rand) {
			size := 20
			sizes := IntSum(r, 2, min(MaxArgsProp, size), size)
			args := make([]*Expr, len(sizes))
			for i, v := range sizes {
				args[i] = GenerateTerm(r, v)
			}
			v[0] = reflect.ValueOf(args)
		},
	}); err != nil {
		t.Error(err)
	}
}
