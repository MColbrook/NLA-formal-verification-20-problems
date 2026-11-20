module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- Finite actual original-row Gram candidates; no threshold facet is added. -/
public import NLA.IV04.PolyhedronSupportReplayR3.OriginalObjectiveAttainment.Domination
public import NLA.IV04.PolyhedronSupportReplayR3.AffinePolyhedronSteps.RationalVertex

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps

theorem original_tight_kernel_point_is_mask_candidate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (x : Fin n → ℝ)
    (hkernel : ∀ d : Fin n → ℝ,
      (∀ i ∈ tightRows (realMatrix A) (realVector b) x, (realMatrix A *ᵥ d) i=0) → d=0) :
    realVector (originalMaskCandidate A b (tightRows (realMatrix A) (realVector b) x))=x := by
  exact (rational_tight_cramer_recovery A b x hkernel).2

theorem mem_feasibleCandidateMasks_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (I : Finset ι) :
    I ∈ feasibleCandidateMasks A b ↔ feasible (realMatrix A) (realVector b)
      (realVector (originalMaskCandidate A b I)) := by
  classical
  simp [feasibleCandidateMasks]

#print axioms original_tight_kernel_point_is_mask_candidate
#print axioms mem_feasibleCandidateMasks_iff
end
end Reference.IV04OriginalObjectiveAttainment
