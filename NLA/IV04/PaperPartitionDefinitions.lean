module

public import NLA.IV04.PaperContinuantDefinitions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace IV04.Paper

/-- The paper's finite input consists of positive integer weights. -/
structure IntegerPartition where
  m : ℕ
  nonempty : 0 < m
  weight : Fin m → ℕ
  positive : ∀ i, 0 < weight i

namespace IntegerPartition

def lastIndex (P : IntegerPartition) : Fin P.m := ⟨P.m-1,Nat.sub_lt P.nonempty (by decide)⟩
def total (P : IntegerPartition) : ℕ := ∑ i, P.weight i
def delta (P : IntegerPartition) : ℚ := 1 / (10 * (P.total : ℚ)^2)
def t (P : IntegerPartition) (i : Fin P.m) : ℚ := P.delta * P.weight i
def c (P : IntegerPartition) (i : Fin P.m) : ℚ := (1-P.t i^2)/(1+P.t i^2)
def s (P : IntegerPartition) (i : Fin P.m) : ℚ := (2*P.t i)/(1+P.t i^2)
def theta (P : IntegerPartition) (i : Fin P.m) : ℝ := 2*Real.arctan (P.t i : ℝ)
def error (P : IntegerPartition) : ℝ := ∑ i, |P.theta i-2*(P.delta : ℝ)*P.weight i|
def signedWeight (P : IntegerPartition) (sign : Fin P.m → ℤ) : ℤ :=
  ∑ i, sign i * (P.weight i : ℤ)
def signedAngle (P : IntegerPartition) (sign : Fin P.m → ℤ) : ℝ :=
  ∑ i, (sign i : ℝ)*P.theta i
def IsSignPattern (P : IntegerPartition) (sign : Fin P.m → ℤ) : Prop :=
  ∀ i, sign i = -1 ∨ sign i = 1
def HasPartition (P : IntegerPartition) : Prop :=
  ∃ sign, P.IsSignPattern sign ∧ P.signedWeight sign = 0
def threshold (P : IntegerPartition) : ℚ := 1-P.delta^2/2

end IntegerPartition

def rotation (theta : ℝ) : Mat 2 :=
  !![Real.cos theta,-Real.sin theta;Real.sin theta,Real.cos theta]

end IV04.Paper
