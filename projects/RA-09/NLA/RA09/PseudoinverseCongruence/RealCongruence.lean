module

public import NLA.RA09.PseudoinverseCongruence.RealSpectral

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder
namespace RootRA09PseudoinverseCongruence
open NLA.RA09

theorem real_outer_action {n : ℕ} (v x : Fin n → ℝ) :
    outerSquare v*ᵥx = (v ⬝ᵥ x) • v := by
  ext i
  simp only [Matrix.mulVec,dotProduct,outerSquare,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem real_outer_quad {n : ℕ} (v x : Fin n → ℝ) :
    x ⬝ᵥ (outerSquare v*ᵥx) = (x ⬝ᵥ v)^2 := by
  rw [real_outer_action,dotProduct_smul,dotProduct_comm v x]
  simp only [smul_eq_mul,pow_two]

theorem real_order_quad {n : ℕ} (X Y : RealMatrix n) (h : X ≤ Y) (v : Fin n → ℝ) :
    v ⬝ᵥ (X*ᵥv) ≤ v ⬝ᵥ (Y*ᵥv) := by
  have hq := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).dotProduct_mulVec_nonneg v
  simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,sub_nonneg] using hq

theorem actual_real_kernel_orthogonality {n : ℕ} {A : RealMatrix n}
    (v x : Fin n → ℝ) (b : ℝ) (hb : 0 < b) (horder : b • outerSquare v ≤ A)
    (hx : A*ᵥx = 0) :
    0 ≤ -b*(x ⬝ᵥ v)^2 ∧ x ⬝ᵥ v = 0 := by
  have hq := real_order_quad (b • outerSquare v) A horder x
  have hq' : b*(x ⬝ᵥ v)^2 ≤ 0 := by
    simpa only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,real_outer_quad,hx,dotProduct_zero] using hq
  refine ⟨by linarith,?_⟩
  by_contra hn
  have hp := mul_pos hb (sq_pos_of_ne_zero hn)
  linarith

theorem actual_real_congruence {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (b : ℝ) (horder : b • outerSquare v ≤ A) :
    b • outerSquare (inverseSqrt A*ᵥv) ≤ supportProjector A := by
  have hw := actual_real_square_root d
  have ht := hw.2.2.2.1
  have hc := hw.2.2.2.2
  have hr : inverseSqrt A*outerSquare v*inverseSqrt A = outerSquare (inverseSqrt A*ᵥv) := by
    simpa only [ht] using outerSquare_conjugate (inverseSqrt A) v
  have h := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr horder)).conjTranspose_mul_mul_same (inverseSqrt A)
  have he : (supportProjector A-b • outerSquare (inverseSqrt A*ᵥv)).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,ht,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,hc,hr] using h
  exact sub_nonneg.mp he.nonneg

theorem actual_real_norm_identity {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) :
    (∑ i, (inverseSqrt A*ᵥv) i ^ 2) = v ⬝ᵥ (spectralPseudoinverse A*ᵥv) := by
  have hw := actual_real_square_root d
  have h := Matrix.dotProduct_transpose_mulVec (inverseSqrt A) v (inverseSqrt A*ᵥv)
  rw [hw.2.2.2.1,Matrix.mulVec_mulVec,hw.2.2.1] at h
  simpa only [dotProduct,pow_two] using h.symm

theorem real_rankOne_bound {n : ℕ} (w : Fin n → ℝ) (b : ℝ)
    (h : b • outerSquare w ≤ (1 : RealMatrix n)) :
    b*(∑ i, w i^2) ≤ 1 := by
  have hs : 0 ≤ ∑ i, w i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  have hq := real_order_quad (b • outerSquare w) 1 h w
  have hd : w ⬝ᵥ w = ∑ i, w i^2 := by simp only [dotProduct,pow_two]
  have hq' : b*(∑ i, w i^2)*(∑ i, w i^2) ≤ ∑ i, w i^2 := by
    simpa only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,real_outer_quad,
      Matrix.one_mulVec,hd,pow_two,← mul_assoc] using hq
  by_cases hz : (∑ i, w i^2) = 0
  · simp [hz]
  · have hp : 0 < ∑ i, w i^2 := lt_of_le_of_ne hs (Ne.symm hz)
    nlinarith

theorem actual_real_harmonic_via_congruence {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (b : ℝ) (hv : ∑ i, v i^2 = 1) (hb : 0 < b)
    (horder : b • outerSquare v ≤ A) :
    v ∈ Set.range (fun x : Fin n → ℝ => A*ᵥx) ∧
      b*(∑ i, (inverseSqrt A*ᵥv) i^2) = b*(v ⬝ᵥ (spectralPseudoinverse A*ᵥv)) ∧
      b*(v ⬝ᵥ (spectralPseudoinverse A*ᵥv)) ≤ 1 := by
  have hc := actual_real_congruence d v b horder
  have hp := (actual_real_support_projector d).2.1
  have hbound := real_rankOne_bound (inverseSqrt A*ᵥv) b (hc.trans hp)
  rw [actual_real_norm_identity d v] at hbound
  exact ⟨(Paper.harmonic_matrix d v b hv hb horder).1,
    congrArg (fun s : ℝ => b*s) (actual_real_norm_identity d v),hbound⟩

#print axioms actual_real_harmonic_via_congruence
end RootRA09PseudoinverseCongruence
