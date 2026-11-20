module

/- Finite actual tight-cardinality maximization; no vertex witness is supplied. -/
public import NLA.IV04.AffinePolyhedronSteps.FiniteStep

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 theorem exists_maximal_tight_point {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (hne : ∃ x, feasible A b x) :
    ∃ x, feasible A b x ∧ ∀ y, feasible A b y →
      (tightRows A b y).card ≤ (tightRows A b x).card := by
  classical
  let attainable : Finset ℕ := (Finset.range (Fintype.card ι+1)).filter
    (fun k => ∃ x, feasible A b x ∧ (tightRows A b x).card=k)
  have hmember : ∀ y, feasible A b y → (tightRows A b y).card ∈ attainable := by
    intro y hy
    simp only [attainable,Finset.mem_filter,Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (tightRows_card_le A b y),⟨y,hy,rfl⟩⟩
  have hnonempty : attainable.Nonempty := by
    obtain ⟨y,hy⟩ := hne
    exact ⟨(tightRows A b y).card,hmember y hy⟩
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image attainable id hnonempty
  obtain ⟨x,hx,hcard⟩ := (Finset.mem_filter.mp hk).2
  refine ⟨x,hx,?_⟩
  intro y hy
  have h := hmax (tightRows A b y).card (hmember y hy)
  simpa only [id_eq,← hcard] using h

 theorem maximal_tight_point_kernel_trivial {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ)
    (hx : feasible A b x) (hline : lineFree A b)
    (hmax : ∀ y, feasible A b y → (tightRows A b y).card ≤ (tightRows A b x).card) :
    ∀ d : Fin n → ℝ, (∀ i ∈ tightRows A b x, (A *ᵥ d) i=0) → d=0 := by
  classical
  intro d hT
  by_contra hd
  have hnonzero : ∃ i, (A *ᵥ d) i ≠ 0 := by
    by_contra hn
    have hz : ∀ i, (A *ᵥ d) i=0 := by simpa only [not_exists,not_not] using hn
    have hall : ∀ t : ℝ, feasible A b (x+t • d) := by
      intro t i
      rw [mulVec_shift,hz i,mul_zero,add_zero]
      exact hx i
    exact hd (hline x d hall)
  obtain ⟨i,hi⟩ := hnonzero
  have hstep : ∃ e : Fin n → ℝ, (∀ j ∈ tightRows A b x, (A *ᵥ e) j=0) ∧
      ∃ j, 0 < (A *ᵥ e) j := by
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · refine ⟨-d,?_,i,?_⟩
      · intro j hj
        simp only [Matrix.mulVec_neg,Pi.neg_apply,hT j hj,neg_zero]
      · simpa only [Matrix.mulVec_neg,Pi.neg_apply] using neg_pos.mpr hneg
    · exact ⟨d,hT,i,hpos⟩
  obtain ⟨e,heT,hepos⟩ := hstep
  obtain ⟨t,ht,hy,hstrict⟩ := finite_boundary_step A b x e hx heT hepos
  have hcard := Finset.card_lt_card hstrict
  have hbound := hmax (x+t • e) hy
  omega

 theorem exists_feasible_trivial_tight_kernel {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (hne : ∃ x, feasible A b x)
    (hline : lineFree A b) :
    ∃ x, feasible A b x ∧ ∀ d : Fin n → ℝ,
      (∀ i ∈ tightRows A b x, (A *ᵥ d) i=0) → d=0 := by
  obtain ⟨x,hx,hmax⟩ := exists_maximal_tight_point A b hne
  exact ⟨x,hx,maximal_tight_point_kernel_trivial A b x hx hline hmax⟩

#print axioms exists_maximal_tight_point
#print axioms maximal_tight_point_kernel_trivial
#print axioms exists_feasible_trivial_tight_kernel
end
end Reference.IV04AffinePolyhedronSteps
