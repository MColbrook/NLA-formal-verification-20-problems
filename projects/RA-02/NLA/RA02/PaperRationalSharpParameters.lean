module

public import NLA.RA02.PaperRationalFamily
public import NLA.RA02.PaperCholeskySup
public import NLA.RA02.PaperLUSup
public import Mathlib.Topology.Instances.Rat

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem exists_positive_rational_parameter (f : ℝ → ℝ) (L : ℝ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 L)) (q : ℝ) (hq : q < L) :
    ∃ t : ℚ, 0 < t ∧ q < f (t : ℝ) := by
  have he : {t : ℝ | q < f t} ∈ 𝓝[>] 0 := hf.eventually (eventually_gt_nhds hq)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhdsWithin_iff.mp he
  obtain ⟨t,ht0,htε⟩ := exists_rat_btwn hε
  refine ⟨t,by exact_mod_cast ht0,hsub ⟨?_,ht0⟩⟩
  change dist (t : ℝ) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_pos ht0]
  exact htε

theorem rational_sharp_cholesky_parameter (r : ℕ) (q : ℝ) (hq : q < (2 : ℝ)^r) :
    ∃ t : ℚ, 0 < t ∧ q <
      NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) (t : ℝ))) r /
        familyRankTail r (t : ℝ) :=
  exists_positive_rational_parameter _ _ (sharp_cholesky_rankTail_limit r) q hq

theorem rational_sharp_lu_parameter (r : ℕ) (q : ℝ) (hq : q < (4 : ℝ)^r) :
    ∃ t : ℚ, 0 < t ∧ q <
      NLA.RA03.expectedError (complexify (sharpFamily (r+1) (t : ℝ))) r /
        rectangularBestRankErrorSquared (complexify (sharpFamily (r+1) (t : ℝ))) r := by
  have hs : Tendsto (fun t : ℝ => NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r /
      rectangularBestRankErrorSquared (complexify (sharpFamily (r+1) t)) r)
      (𝓝[>] 0) (𝓝 ((4 : ℝ)^r)) := by
    simpa only [rectangularBest_eq_squareBest] using sharp_lu_bestApprox_limit r
  exact exists_positive_rational_parameter _ _ hs q hq

#print axioms rational_sharp_lu_parameter
end NLA.RA02.Paper
