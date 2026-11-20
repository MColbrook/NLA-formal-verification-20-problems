module

public import NLA.RA02.PaperMainLimits

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Topology ComplexOrder
open Filter
namespace NLA.RA02.Paper

theorem paper_main_sharp_lower_bound_family (r : ℕ) :
    Tendsto (fun t : ℝ => NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r /
      familyRankTail r t) (𝓝[>] 0) (𝓝 ((2 : ℝ)^r)) ∧
    Tendsto (fun t : ℝ => NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r /
      bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r)
      (𝓝[>] 0) (𝓝 ((4 : ℝ)^r)) ∧
    (∀ᶠ t : ℝ in 𝓝[>] 0, AllSquareMinorsNonzero (sharpFamily (r+1) t)) := by
  exact sharp_lower_bound_family r

theorem paper_main_sharp_lu_bestApprox_limit (r : ℕ) :
    Tendsto (fun t : ℝ => NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r /
      bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r)
      (𝓝[>] 0) (𝓝 ((4 : ℝ)^r)) := by
  exact sharp_lu_bestApprox_limit r

theorem paper_main_bestRankErrorSquared_eq_tail (r : ℕ) (A : NLA.RA02.Square (r+1)) (hA : A.PosDef) :
    bestRankErrorSquared A r = NLA.RA03.singularTailSq A r := by
  exact bestRankErrorSquared_eq_tail r A hA

theorem paper_main_best_error_lower (r : ℕ) (A B : NLA.RA02.Square (r+1))
    (hA : A.PosDef) (hB : B.rank ≤ r) :
    NLA.RA03.singularTailSq A r ≤ NLA.RA03.frobeniusSq (A-B) := by
  exact best_error_lower r A B hA hB

theorem paper_main_best_error_attained (r : ℕ) (A : NLA.RA02.Square (r+1)) (hA : A.PosDef) :
    ∃ B : NLA.RA02.Square (r+1), B.rank ≤ r ∧
      NLA.RA03.frobeniusSq (A-B) = NLA.RA03.singularTailSq A r := by
  exact best_error_attained r A hA

theorem paper_main_sharp_histories_eventually_positive (r : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (∀ h : Fin r ↪ Fin (r+1), 0 < NLA.RA02.pathWeight (complexify (sharpFamily (r+1) t)) (List.ofFn h)) ∧
      (∀ rows cols : Fin r ↪ Fin (r+1),
        0 < NLA.RA03.historyMass (complexify (sharpFamily (r+1) t)) (fun i => some (rows i,cols i))) := by
  exact sharp_histories_eventually_positive r

theorem paper_main_best_error_semantics {n : ℕ} (A : NLA.RA02.Square n) (r : ℕ) :
    bestRankErrorSquared A r = sInf {e : ℝ | ∃ B : NLA.RA02.Square n,
      B.rank ≤ r ∧ (∑ i, ∑ j, Complex.normSq (A i j - B i j)) = e} := by
  rfl

theorem paper_main_rank_tail_semantics (r : ℕ) (t : ℝ)
    (h : (complexify (sharpFamily (r+1) t)).IsHermitian) :
    familyRankTail r t = NLA.RA02.rankTail (complexify (sharpFamily (r+1) t)) h r := by
  simp only [familyRankTail, dif_pos h]

#print axioms NLA.RA02.Paper.paper_main_sharp_lower_bound_family
#print axioms NLA.RA02.Paper.paper_main_sharp_lu_bestApprox_limit
#print axioms NLA.RA02.Paper.paper_main_bestRankErrorSquared_eq_tail
#print axioms NLA.RA02.Paper.paper_main_best_error_lower
#print axioms NLA.RA02.Paper.paper_main_best_error_attained
#print axioms NLA.RA02.Paper.paper_main_sharp_histories_eventually_positive
#print axioms NLA.RA02.Paper.paper_main_best_error_semantics
#print axioms NLA.RA02.Paper.paper_main_rank_tail_semantics
end NLA.RA02.Paper
