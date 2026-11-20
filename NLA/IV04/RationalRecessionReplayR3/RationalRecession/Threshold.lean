module

public import NLA.IV04.RationalRecessionReplayR3.PureDefinitions
/- Actual rational recession ray from unbounded original objectives and repeated threshold vertices. -/
public import NLA.IV04.RationalRecessionReplayR3.RationalRecession.Cramer

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04RationalRecessionRay
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem thresholdBounds_affine {ι : Type*} (b : ι → ℚ) (k : ℚ) :
    thresholdBounds b k=thresholdBounds b 0+k • thresholdDerivativeBounds := by
  funext i
  cases i <;> simp [thresholdBounds,thresholdDerivativeBounds]

theorem threshold_mulVec_inr {ι : Type*} {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (c : Fin n → ℚ) (x : Fin n → ℝ) :
    (realMatrix (thresholdMatrix A c) *ᵥ x) (Sum.inr ())=
      -rowObjective (realVector c) x := by
  simp [realMatrix,thresholdMatrix,Matrix.mulVec,dotProduct,rowObjective,realVector,
    Finset.sum_neg_distrib]

theorem feasible_threshold_iff {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (c : Fin n → ℚ) (k : ℚ) (x : Fin n → ℝ) :
    feasible (realMatrix (thresholdMatrix A c)) (realVector (thresholdBounds b k)) x ↔
      feasible (realMatrix A) (realVector b) x ∧ (k : ℝ) ≤ rowObjective (realVector c) x := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · have hi := h (Sum.inr ())
      rw [threshold_mulVec_inr] at hi
      change -rowObjective (realVector c) x ≤ ((-k : ℚ) : ℝ) at hi
      rw [Rat.cast_neg] at hi
      linarith
  · rintro ⟨hx,hcost⟩ i
    cases i with
    | inl i => exact hx i
    | inr u =>
        cases u
        rw [threshold_mulVec_inr]
        change -rowObjective (realVector c) x ≤ ((-k : ℚ) : ℝ)
        rw [Rat.cast_neg]
        linarith

theorem threshold_lineFree {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (c : Fin n → ℚ) (k : ℚ)
    (hline : lineFree (realMatrix A) (realVector b)) :
    lineFree (realMatrix (thresholdMatrix A c)) (realVector (thresholdBounds b k)) := by
  intro x d hd
  apply hline x d
  intro t
  exact ((feasible_threshold_iff A b c k (x+t • d)).mp (hd t)).1

theorem unbounded_objective_has_rational_recession_mask
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (c : Fin n → ℚ)
    (hline : lineFree (realMatrix A) (realVector b))
    (hunbounded : ∀ K : ℕ, ∃ x, feasible (realMatrix A) (realVector b) x ∧
      (K : ℝ) ≤ rowObjective (realVector c) x) :
    ∃ I : Finset (ι ⊕ Unit), ∃ r : Fin n → ℚ,
      r=originalMaskCandidate (thresholdMatrix A c) thresholdDerivativeBounds I ∧
      r ≠ 0 ∧ (∀ i, (realMatrix A *ᵥ realVector r) i ≤ 0) ∧
      1 ≤ rowObjective (realVector c) (realVector r) := by
  classical
  let D := thresholdMatrix A c
  have hverts : ∀ k : ℕ, ∃ I : Finset (ι ⊕ Unit),
      feasible (realMatrix D) (realVector (thresholdBounds b k))
        (realVector (originalMaskCandidate D (thresholdBounds b k) I)) := by
    intro k
    obtain ⟨x,hx,hcost⟩ := hunbounded k
    have hne : ∃ x, feasible (realMatrix D) (realVector (thresholdBounds b k)) x := by
      refine ⟨x,(feasible_threshold_iff A b c k x).mpr ?_⟩
      exact ⟨hx,by simpa using hcost⟩
    obtain ⟨y,hy,hkernel⟩ := exists_feasible_trivial_tight_kernel
      (realMatrix D) (realVector (thresholdBounds b k)) hne (threshold_lineFree A b c k hline)
    have hrec := original_tight_kernel_point_is_mask_candidate D (thresholdBounds b k) y hkernel
    exact ⟨tightRows (realMatrix D) (realVector (thresholdBounds b k)) y,hrec.symm ▸ hy⟩
  choose masks hmasks using hverts
  obtain ⟨I,hI⟩ := finite_type_has_unbounded_fiber masks
  let u := originalMaskCandidate D (thresholdBounds b 0) I
  let r := originalMaskCandidate D thresholdDerivativeBounds I
  have hp (k : ℕ) (hk : masks k=I) :
      feasible (realMatrix D) (realVector (thresholdBounds b k))
        (realVector u+(k : ℝ) • realVector r) := by
    have hf := hmasks k
    rw [hk,thresholdBounds_affine,originalMaskCandidate_affine,realVector_rational_affine] at hf
    rw [← thresholdBounds_affine] at hf
    simpa using hf
  have hfeas : ∀ k, masks k=I → feasible (realMatrix A) (realVector b)
      (realVector u+(k : ℝ) • realVector r) := by
    intro k hk
    exact ((feasible_threshold_iff A b c k _).mp (hp k hk)).1
  have hcost : ∀ k, masks k=I → (k : ℝ) ≤ rowObjective (realVector c)
      (realVector u+(k : ℝ) • realVector r) := by
    intro k hk
    simpa using ((feasible_threshold_iff A b c k _).mp (hp k hk)).2
  have hdir := affine_feasible_points_yield_recession (realMatrix A) (realVector b)
    (realVector u) (realVector r) (fun k => masks k=I) hI hfeas
  have hpos := affine_thresholds_yield_positive_objective (rowObjective (realVector c))
    (realVector u) (realVector r) (fun k => masks k=I) hI hcost
  have hr : r ≠ 0 := by
    intro hz
    have hzR : realVector (0 : Fin n → ℚ)=(0 : Fin n → ℝ) := by
      funext j
      change ((0 : ℚ) : ℝ)=0
      norm_num
    rw [hz,hzR,map_zero] at hpos
    norm_num at hpos
  exact ⟨I,r,rfl,hr,hdir,hpos⟩

#print axioms thresholdBounds_affine
#print axioms threshold_mulVec_inr
#print axioms feasible_threshold_iff
#print axioms threshold_lineFree
#print axioms unbounded_objective_has_rational_recession_mask
end
end Reference.IV04RationalRecessionRay
