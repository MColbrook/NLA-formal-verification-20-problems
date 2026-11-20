module

public import NLA.RA02.PaperBestErrorDefinitions
public import NLA.RA02.PaperBestApproximationUpper
public import NLA.RA02.PaperHistoryPositivity

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology
open Filter
namespace NLA.RA02.Paper

theorem bestRankErrorSquared_eq_tail (r : ℕ) (A : NLA.RA02.Square (r+1)) (hA : A.PosDef) :
    bestRankErrorSquared A r = NLA.RA03.singularTailSq A r := by
  apply IsLeast.csInf_eq
  constructor
  · exact best_error_attained r A hA
  · rintro e ⟨B,hB,he⟩
    rw [← he]
    exact best_error_lower r A B hA hB

theorem sharp_lu_bestApprox_limit (r : ℕ) :
    Tendsto (fun t : ℝ => NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r /
      bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r)
      (𝓝[>] 0) (𝓝 ((4 : ℝ)^r)) := by
  apply (sharp_lu_singularTail_limit r).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [bestRankErrorSquared_eq_tail r _ (complexify_posDef _ (sharpFamily_posDef _ _ ht))]
  rfl

theorem sharp_lower_bound_family (r : ℕ) :
    Tendsto (fun t : ℝ => NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r /
      familyRankTail r t) (𝓝[>] 0) (𝓝 ((2 : ℝ)^r)) ∧
    Tendsto (fun t : ℝ => NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r /
      bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r)
      (𝓝[>] 0) (𝓝 ((4 : ℝ)^r)) ∧
    (∀ᶠ t : ℝ in 𝓝[>] 0, AllSquareMinorsNonzero (sharpFamily (r+1) t)) := by
  exact ⟨sharp_cholesky_rankTail_limit r, sharp_lu_bestApprox_limit r, sharpFamily_allMinors (r+1)⟩

#print axioms sharp_lower_bound_family
end NLA.RA02.Paper
