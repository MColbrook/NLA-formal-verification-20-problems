module

public import NLA.IV04.PaperCanonicalWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Read the unary length header by recursion on the input bits. -/
def headerWord : List Bool → List Bool
  | [] => []
  | false :: _ => []
  | true :: bits => true :: headerWord bits

def naturalParseRest (input : List Bool) : List Bool :=
  (input.drop (headerWord input).length).tail

def naturalParseFlag (input : List Bool) : List Bool :=
  Complexity.andBit
    (Complexity.nonemptyFlag (input.drop (headerWord input).length))
    (Complexity.notBit (Complexity.nonemptyFlag
      ((headerWord input).drop (naturalParseRest input).length)))

/-- Total parser output: validity flag, raw payload bits, and unused input. -/
def encodedNaturalParser (input : List Bool) : List Bool :=
  let header := headerWord input
  let rest := naturalParseRest input
  Complexity.pair (naturalParseFlag input)
    (Complexity.pair (rest.take header.length) (rest.drop header.length))

end IV04.Paper.Computational
