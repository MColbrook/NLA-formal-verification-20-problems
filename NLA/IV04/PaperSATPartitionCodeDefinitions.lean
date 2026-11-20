module

public import NLA.IV04.PaperSATDigitDefinitions
public import NLA.IV04.PaperSubsetPartitionDefinitions
public import NLA.IV04.PaperInputEncodingDefinitions
public import NLA.IV04.Complexitylib.SAT.Verifier

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational.SATReduction
open Complexity.SAT

/-- A literal Boolean-to-Fin-2 layout, with false at zero and true at one. -/
def boolFinTwo : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i.val = 1)
  left_inv b := by cases b <;> decide
  right_inv i := by
    apply Fin.ext
    have hi := i.isLt
    by_cases h : i.val = 1
    · simp [h]
    · have hz : i.val = 0 := by omega
      simp [hz]

def satSlotCount (φ : CNF) : ℕ :=
  satVariables φ * 2 + φ.length * (satClauseTarget φ-1)

/-- Concrete row-major variable/polarity and clause/slack positions. -/
def satSlotFinEquiv (φ : CNF) : SATSlot φ ≃ Fin (satSlotCount φ) :=
  (Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl (Fin (satVariables φ))) boolFinTwo).trans finProdFinEquiv)
    finProdFinEquiv).trans finSumFinEquiv

def satPartitionIndexEquiv (φ : CNF) : SATSlot φ ⊕ Bool ≃ Fin (satSlotCount φ+2) :=
  (Equiv.sumCongr (satSlotFinEquiv φ) boolFinTwo).trans finSumFinEquiv

def satPartitionWeight (φ : CNF) (i : Fin (satSlotCount φ+2)) : ℕ :=
  subsetPartitionWeights (satSubsetWeights φ) (satSubsetTarget φ)
    ((satPartitionIndexEquiv φ).symm i)

/-- The paper's exact counted canonical binary input format. -/
def countedWeightCode (n : ℕ) (w : Fin n → ℕ) : List Bool :=
  IV04.Paper.naturalCode n ++ (List.ofFn w).flatMap IV04.Paper.naturalCode

def satPartitionCode (φ : CNF) : List Bool :=
  countedWeightCode (satSlotCount φ+2) (satPartitionWeight φ)

def positivePartitionLanguage : Set (List Bool) :=
  {bits | ∃ P : IV04.Paper.IntegerPartition, bits = P.inputCode ∧ P.HasPartition}

/-- Complete input decoder: malformed SAT maps to the fixed no-instance [1,2]. -/
def binarySATPartitionReduction (bits : List Bool) : List Bool :=
  match CNF.decode? bits with
  | none => countedWeightCode 2 ![1,2]
  | some φ => satPartitionCode φ

end IV04.Paper.Computational.SATReduction