module

public import NLA.RA02.PathSemantics

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

theorem cholesky_zero_pivot_contribution {n : ℕ} (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (j : Fin n) (hj : A j j = 0) (w : List (Fin n)) :
    NLA.RA02.pathContribution A (j::w) = 0 := by
  by_cases ht : NLA.RA02.realTrace A = 0
  · have hz := (NLA.RA02.realTrace_eq_zero_iff hA).mp ht
    rw [hz, NLA.RA02.pathContribution_zero]
  · rw [NLA.RA02.pathContribution_cons]
    simp [NLA.RA02.pivotMass, ht, hj]

theorem cholesky_zero_row_contribution {n : ℕ} (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (i : Fin n) (hi : ∀ b, A i b = 0)
    (w : List (Fin n)) (hw : i ∈ w) : NLA.RA02.pathContribution A w = 0 := by
  induction w generalizing A with
  | nil => simp at hw
  | cons j w ih =>
    rcases List.mem_cons.mp hw with hij | him
    · subst j
      exact cholesky_zero_pivot_contribution A hA i (hi i) w
    · rw [NLA.RA02.pathContribution_cons,
        ih (NLA.RA02.choleskyStep A j) (NLA.RA02.choleskyStep_posSemidef A hA j)
          (NLA.RA02.choleskyStep_preserves_zero_row A i j hi) him, mul_zero]

theorem cholesky_repeated_contribution {n : ℕ} (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (w : List (Fin n)) (hw : ¬w.Nodup) :
    NLA.RA02.pathContribution A w = 0 := by
  induction w generalizing A with
  | nil => simp at hw
  | cons j w ih =>
    by_cases hj : A j j = 0
    · exact cholesky_zero_pivot_contribution A hA j hj w
    · by_cases hmem : j ∈ w
      · rw [NLA.RA02.pathContribution_cons,
          cholesky_zero_row_contribution (NLA.RA02.choleskyStep A j)
            (NLA.RA02.choleskyStep_posSemidef A hA j) j
            (NLA.RA02.choleskyStep_pivot_row A j hj) w hmem, mul_zero]
      · have htail : ¬w.Nodup := by simpa [List.nodup_cons, hmem] using hw
        rw [NLA.RA02.pathContribution_cons,
          ih (NLA.RA02.choleskyStep A j) (NLA.RA02.choleskyStep_posSemidef A hA j) htail, mul_zero]

#print axioms cholesky_repeated_contribution
end NLA.RA02.Paper
