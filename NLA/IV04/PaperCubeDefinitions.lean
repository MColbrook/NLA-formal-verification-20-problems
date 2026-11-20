module

public import NLA.IV04.PaperVertexDefinitions
public import NLA.IV04.PaperIntervalDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

def uncertainRow (P : IntegerPartition) (k : Fin (P.m-1)) : Fin P.layerCount :=
  ⟨4*k.val+2,by have := k.isLt; dsimp [layerCount]; omega⟩
def uncertainColumn (P : IntegerPartition) (k : Fin (P.m-1)) : Fin P.layerCount :=
  ⟨4*k.val+1,by have := k.isLt; dsimp [layerCount]; omega⟩

def rationalLower (P : IntegerPartition) : Matrix (Fin P.layerCount) (Fin P.layerCount) ℚ :=
  fun i j => if i=j then P.layerDiagonal i.val else if j.val=i.val+1 then 1 else
    if i.val=j.val+1 then
      if i.val%4=0 then -P.cAt (i.val/4) else
        if i.val%4=1 then -1/P.cAt (i.val/4) else -1
    else 0
def rationalUpper (P : IntegerPartition) : Matrix (Fin P.layerCount) (Fin P.layerCount) ℚ :=
  fun i j => if i.val=j.val+1 ∧ i.val%4=2 then 1 else P.rationalLower i j

end IV04.Paper.IntegerPartition
