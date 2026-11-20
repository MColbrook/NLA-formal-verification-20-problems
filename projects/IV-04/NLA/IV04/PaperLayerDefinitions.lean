module

public import NLA.IV04.PaperPartitionDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

/-- Total extensions only simplify indexing; the matrix uses indices below m. -/
def cAt (P : IntegerPartition) (i : ℕ) : ℚ := if h : i < P.m then P.c ⟨i,h⟩ else 1
def sAt (P : IntegerPartition) (i : ℕ) : ℚ := if h : i < P.m then P.s ⟨i,h⟩ else 0
def thetaAt (P : IntegerPartition) (i : ℕ) : ℝ := if h : i < P.m then P.theta ⟨i,h⟩ else 0
def layerCount (P : IntegerPartition) : ℕ := 4*P.m-2
def layerDiagonal (P : IntegerPartition) (j : ℕ) : ℚ :=
  if j%4=0 then P.sAt (j/4) else
    if j%4=1 then -P.sAt (j/4)/P.cAt (j/4) else 0
def layerBeta (P : IntegerPartition) (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j%4=0 then -(P.cAt (j/4) : ℝ) else
    if j%4=1 then -1/(P.cAt (j/4) : ℝ) else
      if j%4=2 then q (j/4) else -1
def layerMatrix (P : IntegerPartition) (q : ℕ → ℝ) : Mat P.layerCount :=
  continuantMatrix P.layerCount (fun j => (P.layerDiagonal j : ℝ)) (P.layerBeta q)
def reflection (q : ℝ) : Mat 2 := !![1,0;0,-q]
def blockProduct (P : IntegerPartition) (q : ℕ → ℝ) : ℕ → Mat 2
  | 0 => rotation (P.thetaAt 0)
  | k+1 => rotation (P.thetaAt (k+1))*reflection (q k)*P.blockProduct q k

def endpointAngle (P : IntegerPartition) (epsilon : ℕ → ℝ) : ℕ → ℝ
  | 0 => P.thetaAt 0
  | k+1 => P.thetaAt (k+1)+epsilon k*P.endpointAngle epsilon k

end IV04.Paper.IntegerPartition
