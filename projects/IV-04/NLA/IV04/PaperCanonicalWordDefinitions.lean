module

public import NLA.IV04.PaperWordAdderDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Remove high zero padding by a single recursion over the actual input bits. -/
def canonicalWord : List Bool → List Bool
  | [] => []
  | true :: bits => true :: canonicalWord bits
  | false :: bits =>
      let rest := canonicalWord bits
      if rest = [] then [] else false :: rest

/-- Emit the manuscript's length-prefixed canonical natural-number encoding. -/
def canonicalWordCode (bits : List Bool) : List Bool :=
  let normal := canonicalWord bits
  List.replicate normal.length true ++ false :: normal

end IV04.Paper.Computational
