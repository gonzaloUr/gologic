package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"unicode"
)

type Symbol int

const (
	Epsilon Symbol = iota
	Ebnf
	Rule
	Body
	MiddleBody
	FirstConcat0
	FirstConcat
	MiddleConcat0
	MiddleConcat
	Atom
	Optional
	OptionalInside
	EndOptionalInside
	Repetition
	RepetitionInside
	EndRepetitionInside
	Grouping
	GroupingInside
	EndGroupingInside
	Terminal
	DoubleQuotes
	SingleQuotes
	Special
	SpecialInside
	Times
	EmptyWords
	Words
	Whitestuff
	EmptyWord
	Word
	EmptyNumber
	Number
	White
	Letter
	Digit
	Asterisk
	QuestionMark
	SingleQuote
	DoubleQuote
	OpenParentesis
	CloseParentesis
	OpenBracket
	CloseBracket
	OpenSquare
	CloseSquare
	Comma
	Pipe
	Equals
	SemiColon
)

func (s Symbol) String() string {
	switch s {
	case Epsilon:
		return "Epsilon"
	case Ebnf:
		return "Ebnf"
	case Rule:
		return "Rule"
	case Body:
		return "Body"
	case MiddleBody:
		return "MiddleBody"
	case FirstConcat0:
		return "FirstConcat0"
	case FirstConcat:
		return "FirstConcat"
	case MiddleConcat0:
		return "MiddleConcat0"
	case MiddleConcat:
		return "MiddleConcat"
	case Atom:
		return "Atom"
	case Optional:
		return "Optional"
	case OptionalInside:
		return "OptionalInside"
	case Repetition:
		return "Repetition"
	case RepetitionInside:
		return "RepetitionInside"
	case Grouping:
		return "Grouping"
	case GroupingInside:
		return "GroupingInside"
	case Terminal:
		return "Terminal"
	case DoubleQuotes:
		return "DoubleQuotes"
	case SingleQuotes:
		return "SingleQuotes"
	case Special:
		return "Special"
	case SpecialInside:
		return "SpecialInside"
	case Times:
		return "Times"
	case EmptyWords:
		return "EmptyWords"
	case Words:
		return "Words"
	case Whitestuff:
		return "Whitestuff"
	case EmptyWord:
		return "EmptyWord"
	case Word:
		return "Word"
	case EmptyNumber:
		return "EmptyNumber"
	case Number:
		return "Number"
	case White:
		return "White"
	case Letter:
		return "Letter"
	case Digit:
		return "Digit"
	case Asterisk:
		return "Asterisk"
	case QuestionMark:
		return "QuestionMark"
	case SingleQuote:
		return "SingleQuote"
	case DoubleQuote:
		return "DoubleQuote"
	case OpenParentesis:
		return "OpenParentesis"
	case CloseParentesis:
		return "CloseParentesis"
	case OpenBracket:
		return "OpenBracket"
	case CloseBracket:
		return "CloseBracket"
	case OpenSquare:
		return "OpenSquare"
	case CloseSquare:
		return "CloseSquare"
	case Comma:
		return "Comma"
	case Pipe:
		return "Pipe"
	case Equals:
		return "Equals"
	default:
		return "SemiColon"
	}
}

func IsTerminal(symbol Symbol) bool {
	return symbol >= White
}

type Token struct {
	Type   Symbol `json:"type"`
	Value  rune   `json:"value"`
	Pos    int    `json:"pos"`
	Column int    `json:"col"`
	Line   int    `json:"line"`
}

func (t *Token) String() string {
	return string([]rune{t.Value})
}

func Tokenize(input io.Reader) ([]*Token, error) {
	var ret []*Token
	pos, column, line := 1, 1, 1
	s := bufio.NewScanner(input)
	for s.Scan() {
		for _, r := range s.Text() {
			var tokenType Symbol
			if unicode.IsSpace(r) {
				tokenType = White
			} else if unicode.IsLetter(r) {
				tokenType = Letter
			} else if unicode.IsDigit(r) {
				tokenType = Digit
			} else if r == '*' {
				tokenType = Asterisk
			} else if r == '?' {
				tokenType = QuestionMark
			} else if r == '\'' {
				tokenType = SingleQuote
			} else if r == '"' {
				tokenType = DoubleQuote
			} else if r == '(' {
				tokenType = OpenParentesis
			} else if r == ')' {
				tokenType = CloseParentesis
			} else if r == '{' {
				tokenType = OpenBracket
			} else if r == '}' {
				tokenType = CloseBracket
			} else if r == '[' {
				tokenType = OpenSquare
			} else if r == ']' {
				tokenType = CloseSquare
			} else if r == ',' {
				tokenType = Comma
			} else if r == '|' {
				tokenType = Pipe
			} else if r == '=' {
				tokenType = Equals
			} else if r == ';' {
				tokenType = SemiColon
			}
			ret = append(ret, &Token{
				Type:   tokenType,
				Value:  r,
				Pos:    pos,
				Column: column,
				Line:   line,
			})
			pos++
			column++
		}
		pos++
		line++
		column = 1
		ret = append(ret, &Token{
			Type:   White,
			Pos:    pos,
			Column: column,
			Line:   line,
		})
	}
	return ret, nil
}

var Table = map[Symbol]map[Symbol][]Symbol{
	Atom: {
		Digit: {
			Times,
		},
		DoubleQuote: {
			Terminal,
			Whitestuff,
		},
		Letter: {
			Words,
		},
		OpenBracket: {
			Repetition,
			Whitestuff,
		},
		OpenParentesis: {
			Grouping,
			Whitestuff,
		},
		OpenSquare: {
			Optional,
			Whitestuff,
		},
		QuestionMark: {
			Special,
			Whitestuff,
		},
		SingleQuote: {
			Terminal,
			Whitestuff,
		},
	},
	Body: {
		Digit: {
			FirstConcat,
			MiddleBody,
			SemiColon,
		},
		DoubleQuote: {
			FirstConcat,
			MiddleBody,
			SemiColon,
		},
		Letter: {
			FirstConcat,
			MiddleBody,
			SemiColon,
		},
		OpenBracket: {
			FirstConcat,
			MiddleBody,
			SemiColon,
		},
		OpenParentesis: {
			FirstConcat,
			MiddleBody,
			SemiColon,
		},
		OpenSquare: {
			FirstConcat,
			MiddleBody,
			SemiColon,
		},
		QuestionMark: {
			FirstConcat,
			MiddleBody,
			SemiColon,
		},
		SemiColon: {
			SemiColon,
		},
		SingleQuote: {
			FirstConcat,
			MiddleBody,
			SemiColon,
		},
	},
	DoubleQuotes: {
		DoubleQuote: {
			DoubleQuote,
		},
		Letter: {
			Whitestuff,
			Words,
			DoubleQuote,
		},
		White: {
			Whitestuff,
			Words,
			DoubleQuote,
		},
	},
	Ebnf: {
		Epsilon: {},
		Letter: {
			Rule,
			Whitestuff,
			Ebnf,
		},
	},
	EmptyNumber: {
		Asterisk: {},
		Digit: {
			Digit,
			EmptyNumber,
		},
		White: {},
	},
	EmptyWords: {
		CloseBracket:    {},
		CloseParentesis: {},
		CloseSquare:     {},
		Comma:           {},
		DoubleQuote:     {},
		Equals:          {},
		Letter: {
			Letter,
			EmptyWords,
		},
		Pipe:         {},
		QuestionMark: {},
		SemiColon:    {},
		SingleQuote:  {},
		White: {
			White,
			EmptyWords,
		},
	},
	EndGroupingInside: {
		CloseParentesis: {
			CloseParentesis,
		},
		Comma: {
			Comma,
			Whitestuff,
			Atom,
			EndGroupingInside,
		},
	},
	EndOptionalInside: {
		CloseSquare: {
			CloseSquare,
		},
		Comma: {
			Comma,
			Whitestuff,
			Atom,
			EndOptionalInside,
		},
	},
	EndRepetitionInside: {
		CloseBracket: {
			CloseBracket,
		},
		Comma: {
			Comma,
			Whitestuff,
			Atom,
			EndRepetitionInside,
		},
	},
	FirstConcat: {
		Digit: {
			Atom,
			FirstConcat0,
		},
		DoubleQuote: {
			Atom,
			FirstConcat0,
		},
		Letter: {
			Atom,
			FirstConcat0,
		},
		OpenBracket: {
			Atom,
			FirstConcat0,
		},
		OpenParentesis: {
			Atom,
			FirstConcat0,
		},
		OpenSquare: {
			Atom,
			FirstConcat0,
		},
		QuestionMark: {
			Atom,
			FirstConcat0,
		},
		SingleQuote: {
			Atom,
			FirstConcat0,
		},
	},
	FirstConcat0: {
		Comma: {
			Comma,
			Whitestuff,
			Atom,
			FirstConcat0,
		},
		Pipe:      {},
		SemiColon: {},
	},
	Grouping: {
		OpenParentesis: {
			OpenParentesis,
			Whitestuff,
			GroupingInside,
		},
	},
	GroupingInside: {
		CloseParentesis: {
			CloseParentesis,
		},
		Digit: {
			Atom,
			EndGroupingInside,
		},
		DoubleQuote: {
			Atom,
			EndGroupingInside,
		},
		Letter: {
			Atom,
			EndGroupingInside,
		},
		OpenBracket: {
			Atom,
			EndGroupingInside,
		},
		OpenParentesis: {
			Atom,
			EndGroupingInside,
		},
		OpenSquare: {
			Atom,
			EndGroupingInside,
		},
		QuestionMark: {
			Atom,
			EndGroupingInside,
		},
		SingleQuote: {
			Atom,
			EndGroupingInside,
		},
	},
	MiddleBody: {
		Pipe: {
			MiddleConcat,
			MiddleBody,
		},
		SemiColon: {},
	},
	MiddleConcat: {
		Pipe: {
			Pipe,
			Whitestuff,
			Atom,
			MiddleConcat0,
		},
	},
	MiddleConcat0: {
		Comma: {
			Comma,
			Whitestuff,
			Atom,
			MiddleConcat0,
		},
		Pipe:      {},
		SemiColon: {},
	},
	Number: {
		Digit: {
			Digit,
			EmptyNumber,
		},
	},
	Optional: {
		OpenSquare: {
			OpenSquare,
			Whitestuff,
			OptionalInside,
		},
	},
	OptionalInside: {
		CloseSquare: {
			CloseSquare,
		},
		Digit: {
			Atom,
			EndOptionalInside,
		},
		DoubleQuote: {
			Atom,
			EndOptionalInside,
		},
		Letter: {
			Atom,
			EndOptionalInside,
		},
		OpenBracket: {
			Atom,
			EndOptionalInside,
		},
		OpenParentesis: {
			Atom,
			EndOptionalInside,
		},
		OpenSquare: {
			Atom,
			EndOptionalInside,
		},
		QuestionMark: {
			Atom,
			EndOptionalInside,
		},
		SingleQuote: {
			Atom,
			EndOptionalInside,
		},
	},
	Repetition: {
		OpenBracket: {
			OpenBracket,
			Whitestuff,
			RepetitionInside,
		},
	},
	RepetitionInside: {
		CloseBracket: {
			CloseBracket,
		},
		Digit: {
			Atom,
			EndRepetitionInside,
		},
		DoubleQuote: {
			Atom,
			EndRepetitionInside,
		},
		Letter: {
			Atom,
			EndRepetitionInside,
		},
		OpenBracket: {
			Atom,
			EndRepetitionInside,
		},
		OpenParentesis: {
			Atom,
			EndRepetitionInside,
		},
		OpenSquare: {
			Atom,
			EndRepetitionInside,
		},
		QuestionMark: {
			Atom,
			EndRepetitionInside,
		},
		SingleQuote: {
			Atom,
			EndRepetitionInside,
		},
	},
	Rule: {
		Letter: {
			Words,
			Equals,
			Whitestuff,
			Body,
		},
	},
	SingleQuotes: {
		Letter: {
			Whitestuff,
			Words,
			SingleQuote,
		},
		SingleQuote: {
			SingleQuote,
		},
		White: {
			Whitestuff,
			Words,
			SingleQuote,
		},
	},
	Special: {
		QuestionMark: {
			QuestionMark,
			SpecialInside,
		},
	},
	SpecialInside: {
		Letter: {
			Whitestuff,
			Words,
			QuestionMark,
		},
		QuestionMark: {
			QuestionMark,
		},
		White: {
			Whitestuff,
			Words,
			QuestionMark,
		},
	},
	Terminal: {
		DoubleQuote: {
			DoubleQuote,
			DoubleQuotes,
		},
		SingleQuote: {
			SingleQuote,
			SingleQuotes,
		},
	},
	Times: {
		Digit: {
			Number,
			Whitestuff,
			Asterisk,
			Whitestuff,
			Atom,
		},
	},
	Whitestuff: {
		Epsilon:         {},
		Asterisk:        {},
		CloseBracket:    {},
		CloseParentesis: {},
		CloseSquare:     {},
		Comma:           {},
		Digit:           {},
		DoubleQuote:     {},
		Letter:          {},
		OpenBracket:     {},
		OpenParentesis:  {},
		OpenSquare:      {},
		Pipe:            {},
		QuestionMark:    {},
		SemiColon:       {},
		SingleQuote:     {},
		White: {
			White,
			Whitestuff,
		},
	},
	Words: {
		Letter: {
			Letter,
			EmptyWords,
		},
	},
}

type Derivation struct {
	NonTermial Symbol
	Production Symbol
}

func (d *Derivation) String() string {
	return fmt.Sprintf("[%v %v]", d.NonTermial, d.Production)
}

type ParsingError struct {
	Top       Symbol `json:"top"`
	Lookahead *Token `json:"lookahead"`
}

func (p *ParsingError) Error() string {
	return fmt.Sprintf("top %v lookahead %v", p.Top, p.Lookahead)
}

func Parse(tokens []*Token) ([]*Derivation, error) {
	var i int
	var ret []*Derivation
	stack := []Symbol{Ebnf}
	for len(stack) != 0 {
		var lookahead Symbol
		var token *Token
		if i == len(tokens) {
			lookahead = Epsilon
		} else {
			lookahead = tokens[i].Type
			token = tokens[i]
		}
		top := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if !IsTerminal(top) {
			entry, ok := Table[top][lookahead]
			if !ok {
				return nil, &ParsingError{top, token}
			}
			for j := len(entry) - 1; j >= 0; j-- {
				stack = append(stack, entry[j])
			}
			ret = append(ret, &Derivation{NonTermial: top, Production: lookahead})
		} else {
			if top != lookahead {
				return nil, &ParsingError{top, token}
			}
			i++
		}
	}
	return ret, nil
}

type Tree struct {
	NonTerminal Symbol  `json:"non_terminal"`
	Terminal    *Token  `json:"terminal"`
	Children    []*Tree `json:"children"`
}

func (t *Tree) Leaves() []*Tree {
	if len(t.Children) == 0 {
		return []*Tree{t}
	}
	var ret []*Tree
	for _, child := range t.Children {
		ret = append(ret, child.Leaves()...)
	}
	return ret
}

func (t *Tree) String() string {
	var curr string
	if t.Terminal != nil {
		curr = t.Terminal.Type.String()
	} else {
		curr = t.NonTerminal.String()
	}
	if len(t.Children) == 0 {
		return curr
	}
	return fmt.Sprintf("[%s %v]", curr, t.Children)
}

func (t *Tree) Graphviz(w io.Writer) {
	nodes := []*Tree{}
	nodeToName := map[*Tree]string{}
	nodeToLabel := map[*Tree]string{}
	var lastId int
	addNodeData := func(t *Tree) {
		for _, node := range nodes {
			if node == t {
				return
			}
		}
		nodes = append(nodes, t)
		nodeToName[t] = fmt.Sprintf("a%d", lastId)
		lastId++
		if t.Terminal != nil {
			nodeToLabel[t] = t.Terminal.String()
		} else {
			nodeToLabel[t] = t.NonTerminal.String()
		}
	}
	adyacencies := map[*Tree][]*Tree{}
	stack := []*Tree{t}
	for len(stack) != 0 {
		top := stack[0]
		stack = stack[1:]
		addNodeData(top)
		for _, child := range top.Children {
			adyacencies[top] = append(adyacencies[top], child)
			stack = append(stack, child)
		}
	}
	fmt.Fprintf(w, "digraph G {\n")
	for _, node := range nodes {
		fmt.Fprintf(w, "    %s [label=\"%s\"]\n", nodeToName[node], nodeToLabel[node])
	}
	fmt.Fprintln(w)
	for node, children := range adyacencies {
		for _, child := range children {
			fmt.Fprintf(w, "    %s -> %s;\n", nodeToName[node], nodeToName[child])
		}
	}
	fmt.Fprintf(w, "}\n")
}

func AST(tokens []*Token, derivations []*Derivation) *Tree {
	ret := &Tree{NonTerminal: derivations[0].NonTermial}
	var lastToken int
	for _, derivation := range derivations {
		leaves := ret.Leaves()
		var leafToExpand *Tree
		for _, leaf := range leaves {
			if leaf.NonTerminal == derivation.NonTermial {
				leafToExpand = leaf
			}
		}
		rule := Table[derivation.NonTermial][derivation.Production]
		var children []*Tree
		for _, symbol := range rule {
			if IsTerminal(symbol) {
				children = append(children, &Tree{Terminal: tokens[lastToken]})
				lastToken++
			} else {
				children = append(children, &Tree{NonTerminal: symbol})
			}
		}
		leafToExpand.Children = children
	}
	return ret
}

func parseEBNF(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Access-Control-Allow-Origin", "*")
	if r.Method != "POST" {
		return
	}
	tokens, err := Tokenize(r.Body)
	if err != nil {
		fmt.Fprint(w, err)
		return
	}
	derivations, err := Parse(tokens)
	if err != nil {
		out, _ := json.Marshal(err)
		fmt.Fprint(w, string(out))
		return
	}
	out, err := json.Marshal(AST(tokens, derivations))
	if err != nil {
		fmt.Fprint(w, err)
		return
	}
	fmt.Fprint(w, string(out))
}

func main() {
	server := http.Server{
		Addr: "127.0.0.1:9000",
	}
	http.HandleFunc("/parse", parseEBNF)
	server.ListenAndServe()
}
