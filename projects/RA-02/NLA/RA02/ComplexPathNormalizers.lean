module

public import NLA.RA02.ComplexPathDefinitions
public import NLA.RA02.ComplexCholeskyExpectation
public import NLA.RA02.ComplexLUExpectation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper.ComplexHistory

theorem cholesky_normalizer_product {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    NLA.RA02.prefixTraceProduct (A) (List.ofFn h) =
      ∏ s : Fin k, historyTraceNormalizer A h s := by
  unfold NLA.RA02.prefixTraceProduct
  apply Fintype.prod_equiv (finCongr (show (List.ofFn h).length = k from List.length_ofFn))
  intro s
  have hs : s.val < k := by simpa using s.isLt
  rw [take_history h hs.le, choleskyPath_distinct A hA (hs.le.trans hk)]
  rfl

theorem take_pair_history {n k s : ℕ} (rows cols : Fin k ↪ Fin n) (hs : s ≤ k) :
    (List.ofFn (fun i => some (rows i,cols i))).take s =
      List.ofFn (fun i => some (historyPrefix rows hs i,historyPrefix cols hs i)) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hs]
  · intro i hi hj
    simp [historyPrefix]

theorem lu_normalizer_product {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    luNormalizerProduct A (List.ofFn (fun i => some (rows i,cols i))) =
      ∏ s : Fin k, historyFrobeniusNormalizer A rows cols s := by
  rw [luNormalizerProduct_prefixes]
  apply Fintype.prod_equiv (finCongr (show (List.ofFn (fun i => some (rows i,cols i))).length = k from List.length_ofFn))
  intro s
  have hs : s.val < k := by simpa using s.isLt
  rw [take_pair_history rows cols hs.le, luListPath_distinct A hA (hs.le.trans hk)]
  rfl

theorem cholesky_history_identity {k : ℕ} (A : NLA.RA02.Square (k+1))
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef) :
    NLA.RA02.expectedTrace (A) k = A.det.re *
      ∑ h : Fin k ↪ Fin (k+1), ∏ s : Fin k, 1 / historyTraceNormalizer A h s := by
  rw [cholesky_expectation_determinant A hA hpsd]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [cholesky_normalizer_product A hA (Nat.le_succ k) h]
  simp [Finset.prod_inv_distrib]

theorem lu_history_identity {k : ℕ} (A : NLA.RA02.Square (k+1))
    (hA : AllSquareMinorsNonzero A) :
    NLA.RA03.expectedError (A) k = Complex.normSq A.det *
      ∑ rows : Fin k ↪ Fin (k+1), ∑ cols : Fin k ↪ Fin (k+1),
        ∏ s : Fin k, 1 / historyFrobeniusNormalizer A rows cols s := by
  rw [lu_expectation_determinant A hA, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro cols _
  change (luNormalizerProduct A (List.ofFn (fun i => some (rows i,cols i))))⁻¹ = _
  rw [lu_normalizer_product A hA (Nat.le_succ k) rows cols]
  simp [Finset.prod_inv_distrib]

#print axioms lu_history_identity
end NLA.RA02.Paper.ComplexHistory
