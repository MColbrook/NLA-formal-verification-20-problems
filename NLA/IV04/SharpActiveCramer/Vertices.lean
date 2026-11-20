module

/- Every actual finite-inequality extreme point has full active rank and sharp rational size. -/
public import NLA.IV04.SharpActiveCramer.TightSharp

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04SharpActiveCramer
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem exists_positive_feasible_tight_kernel_step
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x d : Fin n → ℝ)
    (hx : feasible A b x)
    (hT : ∀ i ∈ tightRows A b x, (A *ᵥ d) i=0) :
    ∃ t : ℝ, 0<t ∧ feasible A b (x+t • d) := by
  by_cases hp : ∃ i, 0<(A *ᵥ d) i
  · obtain ⟨t,ht,hy,_⟩ := finite_boundary_step A b x d hx hT hp
    exact ⟨t,ht,hy⟩
  · refine ⟨1,by norm_num,?_⟩
    intro i
    rw [mulVec_shift]
    have hn : (A *ᵥ d) i≤0 := le_of_not_gt (fun hi => hp ⟨i,hi⟩)
    have hh := hx i
    linarith

theorem extreme_point_tight_kernel_trivial
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ)
    (hx : x ∈ (feasibleSet A b).extremePoints ℝ) :
    ∀ d : Fin n → ℝ, (∀ i ∈ tightRows A b x, (A *ᵥ d) i=0) → d=0 := by
  rw [mem_extremePoints_iff_left] at hx
  intro d hd
  obtain ⟨t,ht,hy⟩ := exists_positive_feasible_tight_kernel_step A b x d hx.1 hd
  have hneg : ∀ i ∈ tightRows A b x, (A *ᵥ (-d)) i=0 := by
    intro i hi
    simp only [Matrix.mulVec_neg,Pi.neg_apply,hd i hi,neg_zero]
  obtain ⟨u,hu,hz⟩ := exists_positive_feasible_tight_kernel_step A b x (-d) hx.1 hneg
  have hsum : 0<t+u := add_pos ht hu
  have hseg : x ∈ openSegment ℝ (x+t • d) (x+u • (-d)) := by
    refine ⟨u/(t+u),t/(t+u),div_pos hu hsum,div_pos ht hsum,?_,?_⟩
    · field_simp [hsum.ne']
      ring
    · funext j
      simp only [Pi.add_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
      field_simp [hsum.ne']
      ring
  have he : x+t • d=x := hx.2 _ hy _ hz hseg
  funext j
  have hej := congrFun he j
  change x j+t*d j=x j at hej
  have hzj : t*d j=0 := by linarith
  exact (mul_eq_zero.mp hzj).resolve_left ht.ne'

theorem integer_extreme_point_sharp_reduced_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (x : Fin n → ℝ) (H : ℕ)
    (hA : ∀ i j, |A i j|≤(H : ℤ)) (hb : ∀ i, |b i|≤(H : ℤ))
    (hx : x ∈ (feasibleSet (integerRealMatrix A) (integerRealVector b)).extremePoints ℝ) :
    ∃ q : Fin n → ℚ, realVector q=x ∧
      ∀ j, (q j).den≤sharpCertificateBound n H ∧
        (q j).num.natAbs≤sharpCertificateBound n H := by
  exact integer_tight_point_sharp_reduced_certificate A b x H hA hb
    (extreme_point_tight_kernel_trivial _ _ _ hx)

#print axioms exists_positive_feasible_tight_kernel_step
#print axioms extreme_point_tight_kernel_trivial
#print axioms integer_extreme_point_sharp_reduced_certificate
end
end Reference.IV04SharpActiveCramer
