module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- Bounded actual objectives attain a rational original extreme point, using finite original-row candidates. -/
public import NLA.IV04.PolyhedronSupportReplayR3.OriginalObjectiveAttainment.FiniteCandidates

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps

theorem feasibleCandidateMasks_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ)
    (hne : ∃ x, feasible (realMatrix A) (realVector b) x)
    (hline : lineFree (realMatrix A) (realVector b)) :
    (feasibleCandidateMasks A b).Nonempty := by
  obtain ⟨y,hy,hkernel⟩ := exists_feasible_trivial_tight_kernel
    (realMatrix A) (realVector b) hne hline
  have hrec := original_tight_kernel_point_is_mask_candidate A b y hkernel
  refine ⟨tightRows (realMatrix A) (realVector b) y,?_⟩
  rw [mem_feasibleCandidateMasks_iff,hrec]
  exact hy

theorem rational_original_extreme_objective_attained
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ)
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (B : ℝ)
    (hne : ∃ x, feasible (realMatrix A) (realVector b) x)
    (hline : lineFree (realMatrix A) (realVector b))
    (hB : ∀ z, feasible (realMatrix A) (realVector b) z → ℓ z ≤ B) :
    ∃ q : Fin n → ℚ,
      realVector q ∈ (feasibleSet (realMatrix A) (realVector b)).extremePoints ℝ ∧
      (∀ d : Fin n → ℝ,
        (∀ i ∈ tightRows (realMatrix A) (realVector b) (realVector q),
          (realMatrix A *ᵥ d) i=0) → d=0) ∧
      ∀ z, feasible (realMatrix A) (realVector b) z → ℓ z ≤ ℓ (realVector q) := by
  classical
  obtain ⟨I,hI,hmax⟩ := Finset.exists_max_image (feasibleCandidateMasks A b)
    (fun J => ℓ (realVector (originalMaskCandidate A b J)))
    (feasibleCandidateMasks_nonempty A b hne hline)
  have hfeasI := (mem_feasibleCandidateMasks_iff A b I).mp hI
  obtain ⟨y,hy,hcostI,hkernel⟩ := exists_original_extreme_point_dominating
    (realMatrix A) (realVector b) ℓ B (realVector (originalMaskCandidate A b I))
    hfeasI hline hB
  have hrec := original_tight_kernel_point_is_mask_candidate A b y hkernel
  let J := tightRows (realMatrix A) (realVector b) y
  refine ⟨originalMaskCandidate A b J,?_,?_,?_⟩
  · exact hrec.symm ▸ hy
  · exact hrec.symm ▸ hkernel
  · intro z hz
    obtain ⟨w,hw,hwcost,hwkernel⟩ := exists_original_extreme_point_dominating
      (realMatrix A) (realVector b) ℓ B z hz hline hB
    have hwfeas : feasible (realMatrix A) (realVector b) w :=
      ((mem_extremePoints_iff_left).mp hw).1
    have hwrec := original_tight_kernel_point_is_mask_candidate A b w hwkernel
    have hW : tightRows (realMatrix A) (realVector b) w ∈ feasibleCandidateMasks A b := by
      rw [mem_feasibleCandidateMasks_iff,hwrec]
      exact hwfeas
    have hwm := hmax _ hW
    rw [hwrec] at hwm
    change ℓ z ≤ ℓ (realVector (originalMaskCandidate A b
      (tightRows (realMatrix A) (realVector b) y)))
    rw [hrec]
    exact hwcost.trans (hwm.trans hcostI)

#print axioms feasibleCandidateMasks_nonempty
#print axioms rational_original_extreme_objective_attained
end
end Reference.IV04OriginalObjectiveAttainment
