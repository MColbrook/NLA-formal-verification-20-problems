module

public import NLA.PF02.PositiveBasis.Positive
public import NLA.PF02.PaperSymmetricRank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02PositiveBasis
open Matrix NLA.PF02.Paper
open scoped BigOperators MatrixOrder

theorem diagonal_index_count (n : ℕ) :
    (∑ p : SymIndex n, if p.val.1 = p.val.2 then (1 : ℝ) else 0) = n := by
  classical
  let e : {p : SymIndex n // p.val.1 = p.val.2} ≃ Fin n := {
    toFun := fun x => x.val.val.1
    invFun := fun i => ⟨⟨(i,i), le_rfl⟩, rfl⟩
    left_inv := fun x => by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl x.property
    right_inv := fun i => rfl }
  have hc : (Finset.univ.filter (fun p : SymIndex n => p.val.1 = p.val.2)).card = n := by
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr e).trans (Fintype.card_fin n)
  simp only [Finset.sum_boole]
  exact_mod_cast hc

theorem positive_matrices_linearIndependent (n : ℕ) :
    LinearIndependent ℝ (positiveMatrix (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hz p
  let S : ℝ := ∑ q, c q
  have he (q : SymIndex n) :
      S * (2 * (if q.val.1 = q.val.2 then 1 else 0)) + c q * weight q = 0 := by
    have h := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => X q.val.1 q.val.2) hz
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h
    simp_rw [positive_matrix_coordinate, mul_add] at h
    rw [Finset.sum_add_distrib] at h
    simpa [S, ← Finset.sum_mul, eq_comm] using h
  have hcoeff (q : SymIndex n) : c q = if q.val.1 = q.val.2 then -S else 0 := by
    have hq := he q
    by_cases h : q.val.1 = q.val.2
    · simp [weight, h] at hq ⊢
      linarith
    · simp [weight, h] at hq ⊢
      exact hq
  have hsum : S = -S * (n : ℝ) := by
    calc
      S = ∑ q : SymIndex n, if q.val.1 = q.val.2 then -S else 0 := by
        exact Finset.sum_congr rfl (fun q _ => hcoeff q)
      _ = -S * ∑ q : SymIndex n, if q.val.1 = q.val.2 then (1 : ℝ) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        split_ifs <;> simp
      _ = -S * (n : ℝ) := by rw [diagonal_index_count]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : S = 0 := by nlinarith
  rw [hcoeff, hs]
  split_ifs <;> simp

#print axioms diagonal_index_count
#print axioms positive_matrices_linearIndependent
end Reference.PF02PositiveBasis
