module

public import NLA.TR27.PaperGeneralHankel
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

def hankelFeature (D n : ℕ) (t : Option ℂ) : Fin (n+1) → ℂ :=
  match t with
  | some a => fun i => a^i.val
  | none => fun i => if D = 2*n ∧ i.val = n then 1 else 0

theorem sourceHankel_curve {D n : ℕ} (hD : 2*n ≤ D) (t : Option ℂ) :
    sourceHankel n hD (curveVector D t) =
      Matrix.vecMulVec (hankelFeature D n t) (hankelFeature D n t) := by
  ext i j
  cases t with
  | some a => simp [sourceHankel, curveVector, hankelFeature, Matrix.vecMulVec, pow_add]
  | none =>
      have heq : i.val+j.val = D ↔ D = 2*n ∧ i.val = n ∧ j.val = n := by omega
      change (if i.val+j.val = D then (1 : ℂ) else 0) =
        (if D = 2*n ∧ i.val = n then 1 else 0) *
        (if D = 2*n ∧ j.val = n then 1 else 0)
      by_cases hd : D = 2*n <;> by_cases hi : i.val = n <;>
        by_cases hj : j.val = n <;> simp [heq, hd, hi, hj] <;> omega

theorem sourceHankel_sum_rank {D n k : ℕ} (hD : 2*n ≤ D)
    (a : Fin k → ℂ) (t : Fin k → Option ℂ) :
    (sourceHankel n hD (∑ l, a l • curveVector D (t l))).rank ≤ k := by
  let U : Matrix (Fin (n+1)) (Fin k) ℂ := fun i l => a l * hankelFeature D n (t l) i
  let V : Matrix (Fin k) (Fin (n+1)) ℂ := fun l j => hankelFeature D n (t l) j
  have heq : sourceHankel n hD (∑ l, a l • curveVector D (t l)) = U*V := by
    ext i j
    simp only [sourceHankel, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      U, V]
    apply Finset.sum_congr rfl
    intro l _
    have h := congrFun (congrFun (sourceHankel_curve hD (t l)) i) j
    change curveVector D (t l) ⟨i.val+j.val, _⟩ =
      hankelFeature D n (t l) i * hankelFeature D n (t l) j at h
    rw [h, mul_assoc]
  rw [heq]
  exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_width U)

theorem sourceHankel_sum_det_zero {D n k : ℕ} (hD : 2*n ≤ D) (hk : k ≤ n)
    (a : Fin k → ℂ) (t : Fin k → Option ℂ) :
    (sourceHankel n hD (∑ l, a l • curveVector D (t l))).det = 0 := by
  by_contra h
  have hrank := Matrix.rank_of_det_ne_zero h
  have hbound := sourceHankel_sum_rank hD a t
  simp only [Fintype.card_fin] at hrank
  omega

#print axioms sourceHankel_sum_det_zero
end NLA.TR27.Paper
