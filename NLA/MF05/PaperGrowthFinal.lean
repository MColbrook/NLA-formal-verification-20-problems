module

public import NLA.MF05.PaperClosure

@[expose] public section

set_option autoImplicit false
open NLA.MF07
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MF05.Paper

theorem theta_one : theta 1 = 1 := by simp [theta]

theorem theta_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    theta d = (d : ℝ)*(2*Real.exp 1*(d : ℝ)^2/((d : ℝ)-1))^(d-1) := by
  simp [theta, show ¬d ≤ 1 by omega, Nat.cast_sub (show 1 ≤ d by omega)]

theorem complex_bounded_radius_one_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (hr : jointSpectralRadius M = 1) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) := by
  have h := complex_bounded_positive_radius_growth hd M hM hne L hL hML
    (by rw [hr]; norm_num) n hn
  simpa [hr] using h

theorem real_bounded_radius_one_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (hr : realRadius M = 1) (n : ℕ) (hn : 1 ≤ n) :
    realFamilyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) := by
  have h := real_bounded_positive_radius_growth hd M hM hne L hL hML
    (by rw [hr]; norm_num) n hn
  simpa [hr] using h

theorem complex_bounded_comparison {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    familyGrowth M n ≤ (d : ℝ)*s^(d-1) *
      (jointSpectralRadius M + 2*(d : ℝ)^2*L/s)^n := by
  have h := general_quantitative_comparison hd (closure M) hM.isCompact_closure
    (hne.mono subset_closure) L s hL (complex_closure_normBall M L hML) hs n
  simpa only [comparisonFactor, comparisonRate, complex_closure_growth M hM hne,
    complex_closure_radius M hM hne] using h

theorem real_bounded_comparison {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    realFamilyGrowth M n ≤ (d : ℝ)*s^(d-1) *
      (realRadius M + 2*(d : ℝ)^2*L/s)^n := by
  have h := complex_bounded_comparison hd (complexify '' M) (complexify_bounded M hM)
    (hne.image complexify) L hL (complexify_normBall M L hML) s hs n
  simpa only [complexify_growth, complexify_radius] using h

#print axioms complex_bounded_comparison
#print axioms real_bounded_comparison
end NLA.MF05.Paper
