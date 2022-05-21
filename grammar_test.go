package gologic

import "fmt"

func ExampleGrammar_IsLL1() {
	g2 := NewGrammar([][]string{
		{"Rule", "Func", ":-", "Func", "Body"},
		{"Body", ",", "Func", "Body"},
		{"Body"},
		{"Ands", "Func", ",", "Ands"},
		{"Ands"},
		{"Func", "word", "(", "Atom", "Args", ")"},
		{"Args", ",", "Atom", "Args"},
		{"Args"},
		{"Atom", "variable"},
		{"Atom", "constant"},
	})
	fmt.Println(g2.IsLL1())
	table := g2.LL1Table()
	for nonTerminal := range g2.nonTerminals {
		fmt.Printf("%s: ", nonTerminal)
		for terminal := range g2.terminals {
			fmt.Printf("(%s, %s -> %v)", terminal, nonTerminal, table[nonTerminal][terminal])
		}
		fmt.Println()
	}
	// Output:
}
