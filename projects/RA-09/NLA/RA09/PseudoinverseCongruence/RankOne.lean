module

public import NLA.RA09.PseudoinverseCongruence.RealCongruence
public import NLA.RA09.PseudoinverseCongruence.ComplexCongruence

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder ComplexOrder
namespace RootRA09PseudoinverseCongruence

theorem rankOne_action {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (w x : Fin n → 𝕜) (b : 𝕜) :
    (b • Matrix.vecMulVec w (star w))*ᵥx = (b*(star w ⬝ᵥ x)) • w := by
  rw [Matrix.smul_mulVec]
  ext i
  change b*(∑ j, w i * star (w j) * x j) = (b*(∑ j, star (w j)*x j))*w i
  rw [mul_assoc,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem rankOne_rank {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (w : Fin n → 𝕜) (b : 𝕜) :
    Matrix.rank (b • Matrix.vecMulVec w (star w)) ≤ 1 := by
  have he : b • Matrix.vecMulVec w (star w) = Matrix.vecMulVec (b • w) (star w) := by
    ext i j
    simp only [Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

theorem rankOne_eigenvalues {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (w : Fin n → 𝕜) (b : 𝕜)
    (μ : 𝕜) (x : Fin n → 𝕜) (hx : x ≠ 0)
    (he : (b • Matrix.vecMulVec w (star w))*ᵥx = μ • x) :
    μ = 0 ∨ μ = b*(star w ⬝ᵥ w) := by
  have hpoly : (b • Matrix.vecMulVec w (star w))*ᵥ
      ((b • Matrix.vecMulVec w (star w))*ᵥx) =
      (b*(star w ⬝ᵥ w)) • ((b • Matrix.vecMulVec w (star w))*ᵥx) := by
    simp only [rankOne_action,dotProduct_smul,smul_eq_mul,smul_smul]
    congr 1
    ring
  rw [he,Matrix.mulVec_smul,he,smul_smul,smul_smul] at hpoly
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hx (funext hn)
  have hh := congrFun hpoly i
  simp only [Pi.smul_apply,smul_eq_mul] at hh
  have hm : μ*μ = (b*(star w ⬝ᵥ w))*μ := mul_right_cancel₀ hi hh
  have hz : μ*(μ-b*(star w ⬝ᵥ w)) = 0 := by linear_combination hm
  rcases mul_eq_zero.mp hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (sub_eq_zero.mp hz)

theorem actual_real_rankOne_spectrum {n : ℕ} (w : Fin n → ℝ) (b : ℝ) :
    Matrix.rank (b • NLA.RA09.outerSquare w) ≤ 1 ∧
      (b • NLA.RA09.outerSquare w)*ᵥw = (b*(∑ i, w i^2)) • w ∧
      (∀ x : Fin n → ℝ, w ⬝ᵥ x = 0 → (b • NLA.RA09.outerSquare w)*ᵥx = 0) ∧
      (∀ (μ : ℝ) (x : Fin n → ℝ), x ≠ 0 →
        (b • NLA.RA09.outerSquare w)*ᵥx = μ • x → μ = 0 ∨ μ = b*(∑ i, w i^2)) := by
  have he : NLA.RA09.outerSquare w = Matrix.vecMulVec w (star w) := by rfl
  have hd : star w ⬝ᵥ w = ∑ i, w i^2 := by simp only [star_trivial,dotProduct,pow_two]
  refine ⟨by rw [he]; exact rankOne_rank w b,?_,?_,?_⟩
  · rw [he,rankOne_action,hd]
  · intro x hx
    rw [he,rankOne_action]
    simp only [star_trivial,hx,mul_zero,zero_smul]
  · intro μ x hx hμ
    rw [he] at hμ
    simpa only [hd] using rankOne_eigenvalues w b μ x hx hμ

theorem actual_complex_rankOne_spectrum {n : ℕ} (w : Fin n → ℂ) (b : ℝ) :
    Matrix.rank ((b : ℂ) • complexOuterSquare w) ≤ 1 ∧
      ((b : ℂ) • complexOuterSquare w)*ᵥw =
        (((b*(∑ i, Complex.normSq (w i)) : ℝ) : ℂ)) • w ∧
      (∀ x : Fin n → ℂ, star w ⬝ᵥ x = 0 → ((b : ℂ) • complexOuterSquare w)*ᵥx = 0) ∧
      (∀ (μ : ℂ) (x : Fin n → ℂ), x ≠ 0 →
        ((b : ℂ) • complexOuterSquare w)*ᵥx = μ • x →
        μ = 0 ∨ μ = ((b*(∑ i, Complex.normSq (w i)) : ℝ) : ℂ)) := by
  have hd : (b : ℂ)*(star w ⬝ᵥ w) = ((b*(∑ i, Complex.normSq (w i)) : ℝ) : ℂ) := by
    rw [complex_norm_dot,Complex.ofReal_mul]
  refine ⟨rankOne_rank w (b : ℂ),?_,?_,?_⟩
  · change ((b : ℂ) • Matrix.vecMulVec w (star w))*ᵥw = _
    rw [rankOne_action,hd]
  · intro x hx
    change ((b : ℂ) • Matrix.vecMulVec w (star w))*ᵥx = _
    rw [rankOne_action,hx,mul_zero,zero_smul]
  · intro μ x hx hμ
    simpa only [hd] using rankOne_eigenvalues w (b : ℂ) μ x hx hμ

#print axioms actual_real_rankOne_spectrum
#print axioms actual_complex_rankOne_spectrum
end RootRA09PseudoinverseCongruence
