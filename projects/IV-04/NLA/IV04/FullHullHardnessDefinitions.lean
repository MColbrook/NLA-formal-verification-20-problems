module

public import NLA.IV04.PaperFullHullProjectionDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04FullHullHardness
open Complexity IV04.Paper.Computational

def projectFullHullPacket (input : List Bool) : List Bool :=
  pair (pairFst input) (polynomialFirstHullProjection (pairSnd input))

def satFullHullFinish (input : List Bool) : List Bool :=
  polynomialSATHullAnswer (projectFullHullPacket input)

end Reference.IV04FullHullHardness
