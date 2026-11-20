module

public import NLA.RA02.PaperNegativeResults

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Topology ComplexOrder
open Filter
namespace NLA.RA02.Paper

theorem paper_negative_cholesky_real_power_counterexample (C p : ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ t : ℝ, 0 < t ∧
      C * Real.rpow r p * familyRankTail r t <
        NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r := by
  exact cholesky_real_power_counterexample C p

theorem paper_negative_lu_polynomial_counterexample (q : Polynomial ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ t : ℝ, 0 < t ∧
      q.eval (r : ℝ) * (2 : ℝ)^r * bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r <
        NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r := by
  exact lu_polynomial_counterexample q

theorem paper_negative_lu_constant_counterexample (C : ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ t : ℝ, 0 < t ∧
      C * (2 : ℝ)^r * bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r <
        NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r := by
  exact lu_constant_counterexample C

theorem paper_negative_no_uniform_polynomial_cholesky_factor : ¬ NLA.RA02.PolynomialTraceFactor := by
  exact no_uniform_polynomial_cholesky_factor 

theorem paper_negative_no_uniform_polynomial_lu_factor :
    ¬ ∃ q : Polynomial ℝ, ∀ n : ℕ, ∀ A : NLA.RA02.Square n, ∀ r : ℕ,
      1 ≤ r → r ≤ n → NLA.RA03.expectedError A r ≤
        q.eval (r : ℝ) * (2 : ℝ)^r * bestRankErrorSquared A r := by
  exact no_uniform_polynomial_lu_factor 

theorem paper_negative_best_family_error_positive (r : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r := by
  exact best_family_error_positive r ht

theorem paper_negative_complexify_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (complexify A).PosDef := by
  exact complexify_posDef A hA

theorem paper_negative_best_error_semantics {n : ℕ} (A : NLA.RA02.Square n) (r : ℕ) :
    bestRankErrorSquared A r = sInf {e : ℝ | ∃ B : NLA.RA02.Square n,
      B.rank ≤ r ∧ (∑ i, ∑ j, Complex.normSq (A i j - B i j)) = e} := by
  rfl

theorem paper_negative_rank_tail_semantics (r : ℕ) (t : ℝ)
    (h : (complexify (sharpFamily (r+1) t)).IsHermitian) :
    familyRankTail r t = NLA.RA02.rankTail (complexify (sharpFamily (r+1) t)) h r := by
  simp only [familyRankTail, dif_pos h]

#print axioms NLA.RA02.Paper.paper_negative_cholesky_real_power_counterexample
#print axioms NLA.RA02.Paper.paper_negative_lu_polynomial_counterexample
#print axioms NLA.RA02.Paper.paper_negative_lu_constant_counterexample
#print axioms NLA.RA02.Paper.paper_negative_no_uniform_polynomial_cholesky_factor
#print axioms NLA.RA02.Paper.paper_negative_no_uniform_polynomial_lu_factor
#print axioms NLA.RA02.Paper.paper_negative_best_family_error_positive
#print axioms NLA.RA02.Paper.paper_negative_complexify_posDef
#print axioms NLA.RA02.Paper.paper_negative_best_error_semantics
#print axioms NLA.RA02.Paper.paper_negative_rank_tail_semantics
end NLA.RA02.Paper
