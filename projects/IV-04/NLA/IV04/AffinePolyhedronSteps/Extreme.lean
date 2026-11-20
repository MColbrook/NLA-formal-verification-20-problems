module

/- Actual trivial tight kernel makes the actual feasible point an extreme point. -/
public import NLA.IV04.AffinePolyhedronSteps.MaximalTight

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 theorem tight_kernel_implies_extreme {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ)
    (hx : feasible A b x)
    (hkernel : ∀ d : Fin n → ℝ, (∀ i ∈ tightRows A b x, (A *ᵥ d) i=0) → d=0) :
    x ∈ (feasibleSet A b).extremePoints ℝ := by
  rw [mem_extremePoints_iff_left]
  refine ⟨hx,?_⟩
  intro y hy z hz hseg
  obtain ⟨a,c,ha,hc,hac,heq⟩ := hseg
  have hyT : ∀ i ∈ tightRows A b x, (A *ᵥ y) i=b i := by
    intro i hi
    have hxi := (mem_tightRows A b x i).mp hi
    have hrow := congrArg (fun v => (A *ᵥ v) i) heq
    have he : a*(A *ᵥ y) i+c*(A *ᵥ z) i=b i := by
      simpa only [Matrix.mulVec_add,Matrix.mulVec_smul,Pi.add_apply,Pi.smul_apply,
        smul_eq_mul,hxi] using hrow
    have hzbound : c*(A *ᵥ z) i ≤ c*b i := mul_le_mul_of_nonneg_left (hz i) hc.le
    have hsum : a*b i+c*b i=b i := by
      calc
        a*b i+c*b i = (a+c)*b i := by ring
        _ = b i := by rw [hac,one_mul]
    rcases lt_or_eq_of_le (hy i) with hlt | heq
    · have hp := mul_pos ha (sub_pos.mpr hlt)
      nlinarith
    · exact heq
  have hd : y-x=0 := hkernel (y-x) (by
    intro i hi
    simp only [Matrix.mulVec_sub,Pi.sub_apply,hyT i hi,
      (mem_tightRows A b x i).mp hi,sub_self])
  exact sub_eq_zero.mp hd

 theorem exists_extreme_point_of_lineFree {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (hne : ∃ x, feasible A b x)
    (hline : lineFree A b) :
    ∃ x, x ∈ (feasibleSet A b).extremePoints ℝ ∧
      ∀ d : Fin n → ℝ, (∀ i ∈ tightRows A b x, (A *ᵥ d) i=0) → d=0 := by
  obtain ⟨x,hx,hkernel⟩ := exists_feasible_trivial_tight_kernel A b hne hline
  exact ⟨x,tight_kernel_implies_extreme A b x hx hkernel,hkernel⟩

#print axioms tight_kernel_implies_extreme
#print axioms exists_extreme_point_of_lineFree
end
end Reference.IV04AffinePolyhedronSteps
