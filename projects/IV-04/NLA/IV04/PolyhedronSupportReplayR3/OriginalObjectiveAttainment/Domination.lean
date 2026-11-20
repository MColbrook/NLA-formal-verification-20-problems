module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- An original extreme point dominates any feasible point for an actually bounded linear objective. -/
public import NLA.IV04.PolyhedronSupportReplayR3.OriginalObjectiveAttainment.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps

theorem exists_maximal_tight_above
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ)
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → ℝ) (hx : feasible A b x) :
    ∃ y, feasible A b y ∧ ℓ x ≤ ℓ y ∧
      ∀ z, feasible A b z → ℓ x ≤ ℓ z →
        (tightRows A b z).card ≤ (tightRows A b y).card := by
  classical
  let attainable : Finset ℕ := (Finset.range (Fintype.card ι+1)).filter
    (fun k => ∃ y, feasible A b y ∧ ℓ x ≤ ℓ y ∧ (tightRows A b y).card=k)
  have hmember : ∀ y, feasible A b y → ℓ x ≤ ℓ y → (tightRows A b y).card ∈ attainable := by
    intro y hy hxy
    simp only [attainable,Finset.mem_filter,Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (tightRows_card_le A b y),⟨y,hy,hxy,rfl⟩⟩
  have hnonempty : attainable.Nonempty := ⟨_,hmember x hx le_rfl⟩
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image attainable id hnonempty
  obtain ⟨y,hy,hxy,hcard⟩ := (Finset.mem_filter.mp hk).2
  refine ⟨y,hy,hxy,?_⟩
  intro z hz hxz
  have h := hmax (tightRows A b z).card (hmember z hz hxz)
  simpa only [id_eq,← hcard] using h

theorem maximal_tight_above_kernel_trivial
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ)
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (B : ℝ) (x y : Fin n → ℝ)
    (hy : feasible A b y) (hxy : ℓ x ≤ ℓ y) (hline : lineFree A b)
    (hB : ∀ z, feasible A b z → ℓ z ≤ B)
    (hmax : ∀ z, feasible A b z → ℓ x ≤ ℓ z →
      (tightRows A b z).card ≤ (tightRows A b y).card) :
    ∀ d : Fin n → ℝ, (∀ i ∈ tightRows A b y, (A *ᵥ d) i=0) → d=0 := by
  classical
  intro d hT
  by_contra hd
  have hstep : ∃ e : Fin n → ℝ,
      (∀ i ∈ tightRows A b y, (A *ᵥ e) i=0) ∧ 0 ≤ ℓ e ∧
      ∃ i, 0 < (A *ᵥ e) i := by
    rcases lt_trichotomy (ℓ d) 0 with hneg | hzero | hpos
    · refine ⟨-d,?_,?_,?_⟩
      · intro i hi
        simp only [Matrix.mulVec_neg,Pi.neg_apply,hT i hi,neg_zero]
      · simpa only [map_neg] using (neg_pos.mpr hneg).le
      · apply positive_objective_has_positive_row A b ℓ B y (-d) hy
        · simpa only [map_neg] using neg_pos.mpr hneg
        · exact hB
    · have hnonzero : ∃ i, (A *ᵥ d) i ≠ 0 := by
        by_contra hn
        have hz : ∀ i, (A *ᵥ d) i=0 := by simpa only [not_exists,not_not] using hn
        have hall : ∀ t : ℝ, feasible A b (y+t • d) := by
          intro t i
          rw [mulVec_shift,hz i,mul_zero,add_zero]
          exact hy i
        exact hd (hline y d hall)
      obtain ⟨i,hi⟩ := hnonzero
      rcases lt_or_gt_of_ne hi with hminus | hplus
      · refine ⟨-d,?_,?_,i,?_⟩
        · intro j hj
          simp only [Matrix.mulVec_neg,Pi.neg_apply,hT j hj,neg_zero]
        · simp only [map_neg,hzero,neg_zero,le_refl]
        · simpa only [Matrix.mulVec_neg,Pi.neg_apply] using neg_pos.mpr hminus
      · exact ⟨d,hT,hzero.symm.le,i,hplus⟩
    · exact ⟨d,hT,hpos.le,positive_objective_has_positive_row A b ℓ B y d hy hpos hB⟩
  obtain ⟨e,heT,hecost,hepos⟩ := hstep
  obtain ⟨t,ht,hz,hstrict⟩ := finite_boundary_step A b y e hy heT hepos
  have hcost : ℓ x ≤ ℓ (y+t • e) := by
    rw [objective_shift]
    exact hxy.trans (le_add_of_nonneg_right (mul_nonneg ht.le hecost))
  have hcard := Finset.card_lt_card hstrict
  have hbound := hmax (y+t • e) hz hcost
  omega

theorem exists_original_extreme_point_dominating
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ)
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (B : ℝ) (x : Fin n → ℝ)
    (hx : feasible A b x) (hline : lineFree A b)
    (hB : ∀ z, feasible A b z → ℓ z ≤ B) :
    ∃ y, y ∈ (feasibleSet A b).extremePoints ℝ ∧ ℓ x ≤ ℓ y ∧
      ∀ d : Fin n → ℝ, (∀ i ∈ tightRows A b y, (A *ᵥ d) i=0) → d=0 := by
  obtain ⟨y,hy,hxy,hmax⟩ := exists_maximal_tight_above A b ℓ x hx
  have hkernel := maximal_tight_above_kernel_trivial A b ℓ B x y hy hxy hline hB hmax
  exact ⟨y,tight_kernel_implies_extreme A b y hy hkernel,hxy,hkernel⟩

#print axioms exists_maximal_tight_above
#print axioms maximal_tight_above_kernel_trivial
#print axioms exists_original_extreme_point_dominating
end
end Reference.IV04OriginalObjectiveAttainment
