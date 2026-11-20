module

public import NLA.RA09.PseudoinverseCongruence.ComplexSpectral

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder ComplexOrder
namespace RootRA09PseudoinverseCongruence
open NLA.RA09.ComplexPaper

theorem complex_norm_dot {n : ℕ} (w : Fin n → ℂ) :
    star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  simp only [dotProduct,Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,Pi.star_apply,Complex.star_def]

theorem complex_outer_quad {n : ℕ} (v x : Fin n → ℂ) :
    star x ⬝ᵥ (complexOuterSquare v*ᵥx) = (Complex.normSq (star v ⬝ᵥ x) : ℂ) := by
  change star x ⬝ᵥ (outerSquare v*ᵥx) = _
  rw [outerSquare_mulVec,dotProduct_smul]
  have hs : star (star v ⬝ᵥ x) = star x ⬝ᵥ v := by
    simp [dotProduct,star_mul,mul_comm]
  rw [Complex.normSq_eq_conj_mul_self,← Complex.star_def,hs]
  simp only [smul_eq_mul,mul_comm]

theorem complex_order_quad {n : ℕ} (X Y : ComplexMatrix n) (h : X ≤ Y) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (X*ᵥv)).re ≤ (star v ⬝ᵥ (Y*ᵥv)).re := by
  have hq := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).re_dotProduct_nonneg v
  change 0 ≤ (star v ⬝ᵥ ((Y-X)*ᵥv)).re at hq
  simpa only [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re,sub_nonneg] using hq

theorem actual_complex_kernel_orthogonality {n : ℕ} {A : ComplexMatrix n}
    (v x : Fin n → ℂ) (b : ℝ) (hb : 0 < b)
    (horder : (b : ℂ) • complexOuterSquare v ≤ A) (hx : A*ᵥx = 0) :
    0 ≤ -b*Complex.normSq (star v ⬝ᵥ x) ∧ star v ⬝ᵥ x = 0 := by
  have hq := complex_order_quad ((b : ℂ) • complexOuterSquare v) A horder x
  have hq' : b*Complex.normSq (star v ⬝ᵥ x) ≤ 0 := by
    simpa only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,complex_outer_quad,
      hx,dotProduct_zero,← Complex.ofReal_mul,Complex.ofReal_re,Complex.zero_re] using hq
  have hz : Complex.normSq (star v ⬝ᵥ x) = 0 := by
    nlinarith [Complex.normSq_nonneg (star v ⬝ᵥ x)]
  exact ⟨by linarith,Complex.normSq_eq_zero.mp hz⟩

theorem actual_complex_congruence {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℂ) (b : ℝ) (horder : (b : ℂ) • complexOuterSquare v ≤ A) :
    (b : ℂ) • complexOuterSquare (complexInverseSqrt A*ᵥv) ≤ complexSupportProjector A := by
  have hw := actual_complex_square_root d
  have ht := hw.2.2.2.1
  have hc := hw.2.2.2.2
  have hr : complexInverseSqrt A*complexOuterSquare v*complexInverseSqrt A =
      complexOuterSquare (complexInverseSqrt A*ᵥv) := by
    simpa only [ht,complexOuterSquare,outerSquare] using outerSquare_conjugate (complexInverseSqrt A) v
  have h := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr horder)).conjTranspose_mul_mul_same (complexInverseSqrt A)
  have he : (complexSupportProjector A-(b : ℂ) • complexOuterSquare (complexInverseSqrt A*ᵥv)).PosSemidef := by
    simpa only [ht,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hc,hr] using h
  exact sub_nonneg.mp he.nonneg

theorem actual_complex_norm_identity {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℂ) :
    ((∑ i, Complex.normSq ((complexInverseSqrt A*ᵥv) i) : ℝ) : ℂ) =
      star v ⬝ᵥ (spectralPseudoinverse A*ᵥv) := by
  have hw := actual_complex_square_root d
  rw [← complex_norm_dot,Matrix.star_mulVec,hw.2.2.2.1,Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul,hw.2.2.1,← Matrix.dotProduct_mulVec]

theorem complex_rankOne_bound {n : ℕ} (w : Fin n → ℂ) (b : ℝ)
    (h : (b : ℂ) • complexOuterSquare w ≤ (1 : ComplexMatrix n)) :
    b*(∑ i, Complex.normSq (w i)) ≤ 1 := by
  have hs : 0 ≤ ∑ i, Complex.normSq (w i) := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (w i))
  have hq := complex_order_quad ((b : ℂ) • complexOuterSquare w) 1 h w
  have hq' : b*(∑ i, Complex.normSq (w i))*(∑ i, Complex.normSq (w i)) ≤ ∑ i, Complex.normSq (w i) := by
    simpa only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,complex_outer_quad,
      Matrix.one_mulVec,complex_norm_dot,Complex.normSq_ofReal,← Complex.ofReal_mul,
      Complex.ofReal_re,pow_two,← mul_assoc] using hq
  by_cases hz : (∑ i, Complex.normSq (w i)) = 0
  · simp [hz]
  · have hp : 0 < ∑ i, Complex.normSq (w i) := lt_of_le_of_ne hs (Ne.symm hz)
    nlinarith

theorem actual_complex_harmonic_via_congruence {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℂ) (b : ℝ) (hb : 0 < b) (horder : (b : ℂ) • complexOuterSquare v ≤ A) :
    v ∈ Set.range (fun x : Fin n → ℂ => A*ᵥx) ∧
      ((b*(∑ i, Complex.normSq ((complexInverseSqrt A*ᵥv) i)) : ℝ) : ℂ) =
        (b : ℂ)*(star v ⬝ᵥ (spectralPseudoinverse A*ᵥv)) ∧
      (b : ℂ)*(star v ⬝ᵥ (spectralPseudoinverse A*ᵥv)) ≤ 1 := by
  have hc := actual_complex_congruence d v b horder
  have hp := (actual_complex_support_projector d).2.1
  have hbound := complex_rankOne_bound (complexInverseSqrt A*ᵥv) b (hc.trans hp)
  have hn : ((b*(∑ i, Complex.normSq ((complexInverseSqrt A*ᵥv) i)) : ℝ) : ℂ) =
      (b : ℂ)*(star v ⬝ᵥ (spectralPseudoinverse A*ᵥv)) := by
    rw [Complex.ofReal_mul,actual_complex_norm_identity d v]
  refine ⟨(harmonic_matrix d v b hb horder).1,hn,?_⟩
  rw [← hn]
  exact_mod_cast hbound

#print axioms actual_complex_harmonic_via_congruence
end RootRA09PseudoinverseCongruence
