package gologic

import "unicode"

func Concat(a, b [][]string) [][]string {
	var ret [][]string
	for _, x := range a {
		for _, y := range b {
			var entry []string
			entry = append(entry, x...)
			entry = append(entry, y...)
			ret = append(ret, entry)
		}
	}
	return ret
}

func KConcat(k int, a, b [][]string) [][]string {
	var ret [][]string
	for _, x := range a {
		for _, y := range b {
			var entry []string
			for i := 0; i < len(x) && len(entry) < k; i++ {
				entry = append(entry, x[i])
			}
			for i := 0; i < len(y) && len(entry) < k; i++ {
				entry = append(entry, y[i])
			}
			ret = append(ret, entry)
		}
	}
	return ret
}

func Equal(a, b []string) bool {
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

func Union(a, b [][]string) [][]string {
	for _, v := range b {
		var found bool
		for _, u := range a {
			if Equal(u, v) {
				found = true
				break
			}
		}
		if !found {
			a = append(a, v)
		}
	}
	return a
}

func Intersect(a, b [][]string) [][]string {
	var ret [][]string
	for _, v := range a {
		var found bool
		for _, u := range b {
			if Equal(v, u) {
				found = true
				break
			}
		}
		if found {
			ret = append(ret, v)
		}
	}
	return ret
}

type Grammar struct {
	start        string
	rules        map[string][][]string
	terminals    map[string]struct{}
	nonTerminals map[string]struct{}
}

func NewGrammar(rules [][]string) *Grammar {
	rulesMap := map[string][][]string{}
	terminals := map[string]struct{}{}
	nonTerminals := map[string]struct{}{}
	start := rules[0][0]
	for _, rule := range rules {
		nonTerminals[rule[0]] = struct{}{}
		for _, symbol := range rule[1:] {
			if unicode.IsUpper([]rune(symbol)[0]) {
				nonTerminals[symbol] = struct{}{}
			} else {
				terminals[symbol] = struct{}{}
			}
		}
		rulesMap[rule[0]] = append(rulesMap[rule[0]], rule[1:])
	}
	return &Grammar{
		start:        start,
		rules:        rulesMap,
		terminals:    terminals,
		nonTerminals: nonTerminals,
	}
}

func (g *Grammar) IsTerminal(s string) bool {
	_, ok := g.terminals[s]
	return ok
}

func (g *Grammar) IsNonTerminal(s string) bool {
	_, ok := g.nonTerminals[s]
	return ok
}

func (g *Grammar) First(k int) map[string][][]string {
	sets := make(map[string][][]string, len(g.nonTerminals)+len(g.terminals))
	for terminal := range g.terminals {
		sets[terminal] = [][]string{{terminal}}
	}
	for nonTerminal := range g.nonTerminals {
		for _, rule := range g.rules[nonTerminal] {
			var x []string
			for _, symbol := range rule {
				if g.IsTerminal(symbol) {
					x = append(x, symbol)
				} else {
					break
				}
			}
			if len(x) < k && len(x) != len(rule) {
				continue
			}
			sets[nonTerminal] = append(sets[nonTerminal], x)
		}
	}
	hasChanged := true
	for hasChanged {
		hasChanged = false
		newSets := make(map[string][][]string, len(g.nonTerminals)+len(g.terminals))
		for terminal := range g.terminals {
			newSets[terminal] = sets[terminal]
		}
		for nonTerminal := range g.nonTerminals {
			for _, rule := range g.rules[nonTerminal] {
				if len(rule) == 0 {
					continue
				}
				kConcat := make([][]string, len(sets[rule[0]]))
				copy(kConcat, sets[rule[0]])
				for _, symbol := range rule[1:] {
					kConcat = KConcat(k, kConcat, sets[symbol])
				}
				newSets[nonTerminal] = Union(newSets[nonTerminal], kConcat)
			}
			newSets[nonTerminal] = Union(newSets[nonTerminal], sets[nonTerminal])
			if len(newSets[nonTerminal]) > len(sets[nonTerminal]) {
				hasChanged = true
			}
		}
		sets = newSets
	}
	return sets
}

func First(k int, m map[string][][]string, s []string) [][]string {
	if len(s) == 0 {
		return [][]string{nil}
	}
	ret := m[s[0]]
	for _, v := range s[1:] {
		ret = KConcat(k, ret, m[v])
	}
	return ret
}

func FirstSet(k int, m map[string][][]string, set [][]string) [][]string {
	var ret [][]string
	for _, v := range set {
		ret = Union(ret, First(k, m, v))
	}
	return ret
}

func (g *Grammar) Follow(k int) map[string][][]string {
	makeSigma := func() map[string]map[string][][]string {
		ret := make(map[string]map[string][][]string, len(g.nonTerminals))
		for x := range g.nonTerminals {
			ret[x] = make(map[string][][]string, len(g.nonTerminals))
			for y := range g.nonTerminals {
				ret[x][y] = nil
			}
		}
		return ret
	}
	first := g.First(k)
	sigma := makeSigma()
	for x := range g.nonTerminals {
		for y := range g.nonTerminals {
			for _, rule := range g.rules[x] {
				for i, v := range rule {
					if v == y {
						sigma[x][y] = Union(sigma[x][y], First(k, first, rule[i+1:]))
					}
				}
			}
		}
	}
	hasChanged := true
	for hasChanged {
		hasChanged = false
		newSigma := makeSigma()
		for x := range g.nonTerminals {
			for y := range g.nonTerminals {
				newSigma[x][y] = Union(newSigma[x][y], sigma[x][y])
				for _, rule := range g.rules[x] {
					for i, v := range rule {
						if g.IsNonTerminal(v) {
							toUnion := make([][]string, len(sigma[v][y]))
							copy(toUnion, sigma[v][y])
							toUnion = KConcat(k, toUnion, First(k, first, rule[i+1:]))
							newSigma[x][y] = Union(newSigma[x][y], toUnion)
						}
					}
				}
				if len(newSigma[x][y]) > len(sigma[x][y]) {
					hasChanged = true
				}
			}
		}
		sigma = newSigma
	}
	ret := make(map[string][][]string, len(g.nonTerminals))
	for x := range g.nonTerminals {
		ret[x] = sigma[g.start][x]
	}
	return ret
}

type LL1Conflict struct {
	NonTerminal string
	Production1 []string
	Production2 []string
}

func (g *Grammar) IsLL1() *LL1Conflict {
	first := g.First(1)
	follow := g.Follow(1)
	for nonTerminal := range g.nonTerminals {
		for i, beta := range g.rules[nonTerminal] {
			for _, alpha := range g.rules[nonTerminal][i+1:] {
				s1 := FirstSet(1, first, Concat([][]string{beta}, follow[nonTerminal]))
				s2 := FirstSet(1, first, Concat([][]string{alpha}, follow[nonTerminal]))
				if len(Intersect(s1, s2)) != 0 {
					return &LL1Conflict{
						NonTerminal: nonTerminal,
						Production1: beta,
						Production2: alpha,
					}
				}
			}
		}
	}
	return nil
}

type LL1TableEntry struct {
	NonTerminal string
	RuleIndex   int
	IsPop       bool
	IsAccept    bool
}

func (g *Grammar) LL1Table() map[string]map[string]*LL1TableEntry {
	ret := make(map[string]map[string]*LL1TableEntry, len(g.nonTerminals))
	for nonTerminal := range g.nonTerminals {
		ret[nonTerminal] = map[string]*LL1TableEntry{}
	}
	first := g.First(1)
	follow := g.Follow(1)
	for nonTerminal := range g.nonTerminals {
		for i, rule := range g.rules[nonTerminal] {
			var empty bool
			for _, v := range First(1, first, rule) {
				if len(v) == 0 {
					empty = true
					continue
				}
				ret[nonTerminal][v[0]] = &LL1TableEntry{
					NonTerminal: nonTerminal,
					RuleIndex:   i,
				}
			}
			if empty {
				for _, v := range follow[nonTerminal] {
					if len(v) == 0 {
						continue
					}
					ret[nonTerminal][v[0]] = &LL1TableEntry{
						NonTerminal: nonTerminal,
						RuleIndex:   i,
					}
				}
			}
		}
	}
	return ret
}
