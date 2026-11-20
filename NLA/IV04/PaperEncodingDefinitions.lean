module

public import NLA.IV04.PaperBinaryDefinitions
public import NLA.IV04.PaperCubeDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper

/-- Unary length followed by the canonical least-significant-first payload. -/
def naturalCode (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0,rest)
  | true :: rest => do
      let (n,tail) ← readUnary rest
      return (n+1,tail)

def readNatural (bits : List Bool) : Option (ℕ × List Bool) := do
  let (n,tail) ← readUnary bits
  if n ≤ tail.length then
    return ((tail.take n).foldr Nat.bit 0,tail.drop n)
  else none

def rationalCode (q : ℚ) : List Bool :=
  decide (q.num < 0) :: (naturalCode q.num.natAbs ++ naturalCode q.den)

def readRational : List Bool → Option (ℚ × List Bool)
  | [] => none
  | sign :: rest => do
      let (num,tail) ← readNatural rest
      let (den,last) ← readNatural tail
      let signed : ℤ := if sign then -(num : ℤ) else (num : ℤ)
      return ((signed : ℚ)/(den : ℚ),last)

namespace IntegerPartition

/-- Row-major dense encoding of both actual endpoints and the actual threshold. -/
def matrixBoxCode (P : IntegerPartition) : List Bool :=
  naturalCode P.layerCount ++
  (List.finRange P.layerCount).flatMap (fun i =>
    (List.finRange P.layerCount).flatMap (fun j =>
      rationalCode (P.rationalLower i j) ++ rationalCode (P.rationalUpper i j))) ++
  rationalCode P.threshold

end IntegerPartition
end IV04.Paper
