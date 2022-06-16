package gologic

import (
	"encoding/json"
	"fmt"
)

func PrintFirst(g *Grammar) {
	firsts := g.First(1)
	for nonTerminal := range g.nonTerminals {
		fmt.Printf("FIRST(%s) = %v\n", nonTerminal, firsts[nonTerminal])
	}
}

func PrintFollow(g *Grammar) {
	follows := g.Follow(1)
	for nonTerminal := range g.nonTerminals {
		fmt.Printf("FOLLOW(%s) = %v\n", nonTerminal, follows[nonTerminal])
	}
}

func ExampleGrammar_IsLL1() {
	g := NewGrammar([][]string{
		{"Ebnf"},
		{"Ebnf", "Rule", "Whitestuff", "Ebnf"},

		{"Rule", "Words", "equals", "Whitestuff", "Body"},

		{"Body", "semiColon"},
		{"Body", "FirstConcat", "MiddleBody", "semiColon"},

		{"MiddleBody"},
		{"MiddleBody", "MiddleConcat", "MiddleBody"},

		{"FirstConcat0"},
		{"FirstConcat0", "comma", "Whitestuff", "Atom", "FirstConcat0"},
		{"FirstConcat", "Atom", "FirstConcat0"},

		{"MiddleConcat0"},
		{"MiddleConcat0", "comma", "Whitestuff", "Atom", "MiddleConcat0"},
		{"MiddleConcat", "pipe", "Whitestuff", "Atom", "MiddleConcat0"},

		{"Atom", "Optional", "Whitestuff"},
		{"Atom", "Repetition", "Whitestuff"},
		{"Atom", "Grouping", "Whitestuff"},
		{"Atom", "Terminal", "Whitestuff"},
		{"Atom", "Special", "Whitestuff"},
		{"Atom", "Times"},
		{"Atom", "Words"},

		{"Optional", "openSquare", "Whitestuff", "OptionalInside"},
		{"OptionalInside", "closeSquare"},
		{"OptionalInside", "Atom", "EndOptionalInside"},
		{"EndOptionalInside", "closeSquare"},
		{"EndOptionalInside", "comma", "Whitestuff", "Atom", "EndOptionalInside"},

		{"Repetition", "openBracket", "Whitestuff", "RepetitionInside"},
		{"RepetitionInside", "closeBracket"},
		{"RepetitionInside", "Atom", "EndRepetitionInside"},
		{"EndRepetitionInside", "closeBracket"},
		{"EndRepetitionInside", "comma", "Whitestuff", "Atom", "EndRepetitionInside"},

		{"Grouping", "openParen", "Whitestuff", "GroupingInside"},
		{"GroupingInside", "closeParen"},
		{"GroupingInside", "Atom", "EndGroupingInside"},
		{"EndGroupingInside", "closeParen"},
		{"EndGroupingInside", "comma", "Whitestuff", "Atom", "EndGroupingInside"},

		{"Terminal", "doubleQuote", "DoubleQuotes"},
		{"DoubleQuotes", "doubleQuote"},
		{"DoubleQuotes", "Whitestuff", "Words", "doubleQuote"},

		{"Terminal", "singleQuote", "SingleQuotes"},
		{"SingleQuotes", "singleQuote"},
		{"SingleQuotes", "Whitestuff", "Words", "singleQuote"},

		{"Special", "questionMark", "SpecialInside"},
		{"SpecialInside", "questionMark"},
		{"SpecialInside", "Whitestuff", "Words", "questionMark"},

		{"Times", "Number", "Whitestuff", "asterisk", "Whitestuff", "Atom"},

		{"EmptyWords"},
		{"EmptyWords", "letter", "EmptyWords"},
		{"EmptyWords", "white", "EmptyWords"},
		{"Words", "letter", "EmptyWords"},

		{"Whitestuff"},
		{"Whitestuff", "white", "Whitestuff"},

		{"EmptyNumber"},
		{"EmptyNumber", "digit", "EmptyNumber"},
		{"Number", "digit", "EmptyNumber"},
	})
	if conflict := g.IsLL1(); conflict != nil {
		fmt.Printf("NonTerminal: %s\n", conflict.NonTerminal)
		fmt.Printf("Production: %s\n", conflict.Production1)
		fmt.Printf("Production: %s\n", conflict.Production2)
		fmt.Println()
	} else {
		b, err := json.MarshalIndent(g.LL1Table("Epsilon"), "", "  ")
		if err != nil {
			panic(err)
		}
		fmt.Println(string(b))
	}
	PrintFirst(g)
	fmt.Println()
	PrintFollow(g)
	// Output:
	// nil
}
