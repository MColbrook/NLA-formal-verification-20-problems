module

public import NLA.TR27.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

abbrev CurveSpace (D : ℕ) := Fin (D + 1) → ℂ

/-- The actual degree-D rational normal curve, with its point at infinity. -/
def curveVector (D : ℕ) : Option ℂ → CurveSpace D
  | some t => fun j => t ^ (j : ℕ)
  | none => fun j => if (j : ℕ) = D then 1 else 0

def tangentVector (D : ℕ) : CurveSpace D := fun j => if (j : ℕ) = 1 then 1 else 0

theorem tangentVector_nonzero (D : ℕ) (hD : 2 ≤ D) : tangentVector D ≠ 0 := by
  intro h
  have hindex : 1 < D + 1 := Nat.lt_succ_of_le (le_trans (by decide : 1 ≤ 2) hD)
  have heq := congrFun h (⟨1, hindex⟩ : Fin (D+1))
  simp [tangentVector] at heq

def tangentPoint (D : ℕ) (hD : 2 ≤ D) : ℙ ℂ (CurveSpace D) :=
  Projectivization.mk ℂ (tangentVector D) (tangentVector_nonzero D hD)

/-- Projective curve points represented by (1,t,...,t^D) and e_D. -/
def curvePoints (D : ℕ) : Set (ℙ ℂ (CurveSpace D)) :=
  {p | ∃ t : Option ℂ, Represents (curveVector D t) p}

end NLA.TR27.Paper
