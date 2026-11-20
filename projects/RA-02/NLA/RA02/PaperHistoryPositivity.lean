module

public import NLA.RA02.PaperHistoryLimits

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology
open Filter
namespace NLA.RA02.Paper

theorem cholesky_distinct_weight_positive {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef) (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    0 < NLA.RA02.pathWeight (complexify A) (List.ofFn h) := by
  have hc := complexify_posSemidef A hpsd
  have ht := cholesky_distinct_prefix_trace A hA hc hk h
  have hn : NLA.RA02.pathWeight (complexify A) (List.ofFn h) ≠ 0 := by
    rw [cholesky_pathWeight_det A hA hk h ht]
    apply div_ne_zero (hA k hk h h)
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    exact ht s
  exact lt_of_le_of_ne (NLA.RA02.pathWeight_nonneg _ hc _) hn.symm

theorem luNormalizerProduct_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (w : List (Option (Fin n × Fin n))) : 0 ≤ luNormalizerProduct A w := by
  induction w generalizing A with
  | nil => exact zero_le_one
  | cons p w ih =>
    rw [luNormalizerProduct, complexify_frobenius]
    exact mul_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j))))
      (ih (realLUNext A p))

theorem lu_distinct_weight_positive {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    0 < NLA.RA03.historyMass (complexify A) (fun i => some (rows i,cols i)) := by
  rw [actual_luMass_det A hA hk rows cols]
  apply div_pos (sq_pos_of_ne_zero (hA k hk rows cols))
  exact lt_of_le_of_ne (luNormalizerProduct_nonneg A _) (luMass_det A hA hk rows cols).1.symm

theorem sharp_histories_eventually_positive (r : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (∀ h : Fin r ↪ Fin (r+1), 0 < NLA.RA02.pathWeight (complexify (sharpFamily (r+1) t)) (List.ofFn h)) ∧
      (∀ rows cols : Fin r ↪ Fin (r+1),
        0 < NLA.RA03.historyMass (complexify (sharpFamily (r+1) t)) (fun i => some (rows i,cols i))) := by
  filter_upwards [sharpFamily_allMinors (r+1), self_mem_nhdsWithin] with t ha ht
  constructor
  · intro h
    exact cholesky_distinct_weight_positive _ ha (sharpFamily_posDef _ _ ht).posSemidef (Nat.le_succ r) h
  · intro rows cols
    exact lu_distinct_weight_positive _ ha (Nat.le_succ r) rows cols

#print axioms sharp_histories_eventually_positive
end NLA.RA02.Paper
