package gologic

import (
	"math/rand"
	"reflect"
	"testing"
	"testing/quick"
	"time"
)

const (
	MaxArgsFunc = 3
	MaxArgsProp = 3
	MaxId       = 5
)

func GenerateTerm(rand *rand.Rand, size int) *Expr {
	var choice int
	if size <= 1 {
		choice = rand.Intn(2)
	} else {
		choice = rand.Intn(3)
	}
	switch choice {
	case 0:
		return Const(uint(rand.Intn(MaxId)))
	case 1:
		return Var(uint(rand.Intn(MaxId)))
	default:
		return Func(uint(rand.Intn(MaxId)), GenerateTerms(rand, size)...)
	}
}

func ArgsSize(rand *rand.Rand, size int) []int {
	cantArgs := rand.Intn(min(MaxArgsFunc, size)) + 1
	argsSize := make([]int, cantArgs)
	for i := range argsSize {
		argsSize[i] = 1
	}
	for i := 0; i < size-(cantArgs+1); i++ {
		toInc := rand.Intn(cantArgs)
		argsSize[toInc]++
	}
	return argsSize
}

func GenerateTerms(rand *rand.Rand, size int) []*Expr {
	if size == 0 {
		return []*Expr{}
	}
	argsSize := ArgsSize(rand, size)
	args := make([]*Expr, len(argsSize))
	for i, v := range argsSize {
		args[i] = GenerateTerm(rand, v)
	}
	return args
}

func GenerateForm(rand *rand.Rand, size int) *Expr {
	if size <= 1 {
		return Prop(uint(rand.Intn(MaxId)), GenerateTerms(rand, size)...)
	}
	switch rand.Intn(8) {
	case 0:
		return Prop(uint(rand.Intn(MaxId)), GenerateTerms(rand, size-1)...)
	case 1:
		return Not(GenerateForm(rand, size-1))
	case 2:
		return Forall(uint(rand.Intn(MaxId)), GenerateForm(rand, size-1))
	case 3:
		return Exists(uint(rand.Intn(MaxId)), GenerateForm(rand, size-1))
	case 4:
		return And(GenerateForms(rand, size))
	case 5:
		return Or(GenerateForms(rand, size))
	case 6:
		return Iff(GenerateForms(rand, size))
	default:
		return Then(GenerateForms(rand, size))
	}
}

func GenerateForms(rand *rand.Rand, size int) (*Expr, *Expr) {
	fstArgSize := rand.Intn(size) + 1
	sndArgSize := size - fstArgSize
	return GenerateForm(rand, fstArgSize), GenerateForm(rand, sndArgSize)
}

func (*Expr) Generate(rand *rand.Rand, size int) reflect.Value {
	return reflect.ValueOf(GenerateForm(rand, size))
}

type Form Expr

func (*Form) Generate(rand *rand.Rand, size int) reflect.Value {
	return reflect.ValueOf((*Form)(GenerateForm(rand, size)))
}

func (f *Form) String() string {
	return (*Expr)(f).String()
}

type Term Expr

func (*Term) Generate(rand *rand.Rand, size int) reflect.Value {
	return reflect.ValueOf((*Term)(GenerateTerm(rand, size)))
}

func (t *Term) Stirng() string {
	return (*Expr)(t).String()
}

func pow(b, n int) int {
	ret := 1
	for i := 0; i < n; i++ {
		ret *= b
	}
	return ret
}

// Returns all the repeating permutations with the passed length of the selected elements
// from set using elems with len(elems) = length such that elems[i] selects set[elems[i]]
// from the set.
//
// eg:
// RepeatingPermutation(3, []uint{0, 1, 2}, map[uint]{0: 4, 1: 5, 2: 6}) =
// [[4, 4, 4], [4, 4, 5], [4, 4, 6], [4, 5, 4], ... ]
func RepeatingPermutation[T comparable](length int, elems []uint, set map[uint]T) [][]T {
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
					ret[permIndex][permElemInx] = set[elems[currElem]]
					permIndex++
				}
			}
		}
	}
	return ret
}

func allEqual[T comparable](a, b []T) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

type propResult[T comparable] struct {
	args  []T
	value bool
}

func CreateProp[T comparable](prop map[int][]*propResult[T]) func([]T) bool {
	return func(args []T) bool {
		for _, v := range prop[len(args)] {
			if allEqual(v.args, args) {
				return v.value
			}
		}
		panic("no entry found for passed args")
	}
}

func CreateFunc[T comparable](fn map[int][][]T) func([]T) T {
	return func(args []T) T {
		for _, v := range fn[len(args)] {
			if allEqual(v[:len(v)-1], args) {
				return v[len(args)-1]
			}
		}
		panic("no entry found for passed args")
	}
}

func (*Model[T]) Generate(rand *rand.Rand, size int) reflect.Value {
	tType := reflect.TypeOf((*T)(nil)).Elem()
	// eg: constants[2] = T means that [c2] = T
	constants := make(map[uint]T, MaxId)
	for i := uint(0); i < MaxId; i++ {
		c, ok := quick.Value(tType, rand)
		if !ok {
			panic("cannot generate value for type " + tType.String())
		}
		constants[i] = c.Interface().(T)
	}
	// eg: functionsMap[2][3] = {T1, T2, T3, T4} represents that f2(T1, T2, T3) = T4.
	functionsMap := make(map[uint]map[int][][]T, MaxId)
	for i := uint(0); i < MaxId; i++ {
		functionsMap[i] = make(map[int][][]T, MaxArgsFunc)
	}
	for k := range functionsMap {
		functionsMap[k] = make(map[int][][]T, MaxArgsFunc)
	}
	elems := make([]uint, MaxId)
	for i := range elems {
		elems[i] = uint(i)
	}
	for functionId := uint(0); functionId < MaxId; functionId++ {
		for length := 1; length <= MaxArgsFunc; length++ {
			perm := RepeatingPermutation(length, elems, constants)
			for k, v := range perm {
				perm[k] = append(v, constants[uint(rand.Intn(MaxId))])
			}
			functionsMap[functionId][length] = perm
		}
	}
	// eg: propositionsMap[2][3] = {args: {T1, T2, T3}, value: true} represents that
	// [P2(T1, T2, T3)] = 1.
	propositionsMap := map[uint]map[int][]*propResult[T]{}
	for i := uint(0); i < MaxId; i++ {
		propositionsMap[i] = make(map[int][]*propResult[T], MaxArgsProp)
	}
	for propId := uint(0); propId < MaxId; propId++ {
		value := false
		if rand.Intn(2) == 0 {
			value = true
		}
		propositionsMap[propId][0] = []*propResult[T]{{args: []T{}, value: value}}
		for length := 1; length <= MaxArgsProp; length++ {
			perm := RepeatingPermutation(length, elems, constants)
			entries := make([]*propResult[T], len(perm))
			for k, v := range perm {
				value := false
				if rand.Intn(2) == 0 {
					value = true
				}
				entries[k] = &propResult[T]{args: v, value: value}
			}
			propositionsMap[propId][length] = entries
		}
	}
	functions := make(map[uint]func([]T) T, MaxId)
	for k := uint(0); k < MaxId; k++ {
		functions[k] = CreateFunc(functionsMap[k])
	}
	propositions := make(map[uint]func([]T) bool, MaxId)
	for k := uint(0); k < MaxId; k++ {
		propositions[k] = CreateProp(propositionsMap[k])
	}
	return reflect.ValueOf(&Model[T]{
		Constants:    constants,
		Functions:    functions,
		Propositions: propositions,
	})
}

func TestClosure(t *testing.T) {
	prop := func(f *Form, m *Model[int]) bool {
		e := (*Expr)(f)
		return len(e.Closure().FreeVars()) == 0
	}
	r := rand.New(rand.NewSource(time.Now().UnixNano()))
	if err := quick.Check(prop, &quick.Config{Rand: r}); err != nil {
		t.Errorf("%v", err)
	}
}
