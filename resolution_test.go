package gologic

import "fmt"

func ExampleMGU() {
	a := Prop(0, Const(0), Var(0), Func(0, Func(1, Var(1))))
	b := Prop(0, Var(2), Func(0, Var(2)), Func(0, Var(3)))
	s := MGU(a, b)
	fmt.Println(s)
	// Output:
	// {f1(x1)/x3, f0(c0)/x0, c0/x2}
}

func ExampleResolve() {
	a := []*Expr{Prop(0, Var(0)), Prop(1, Var(0))}
	b := []*Expr{Not(Prop(0, Const(0))), Prop(2, Var(1))}
	r := Resolve(a, b, 0, 0)
	fmt.Println(r.Result)
	// Output:
}

func ExampleSLD() {
	prog := &SLD{
		[]*Rule{
			{Prop(4, Const(1)), []*Expr{}},
			{Prop(0, Var(0)), []*Expr{Prop(1, Var(0))}},
			{Prop(1, Var(1)), []*Expr{Prop(2, Var(1))}},
			{Prop(2, Var(2)), []*Expr{Prop(3, Var(2))}},
			{Prop(3, Var(3)), []*Expr{Prop(4, Var(3))}},
		},
		[]*Expr{Prop(0, Var(4))},
	}
	fmt.Println(Run(prog))
	// Output:
}
