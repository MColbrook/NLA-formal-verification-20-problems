module

public import NLA.MF05.PaperGrowthFinal

@[expose] public section

set_option autoImplicit false
open scoped Topology Matrix.Norms.L2Operator
open NLA.MF07 Filter
noncomputable section
namespace NLA.MF05.Paper

theorem paper_complex_closure_growth {d : ℕ} (M : Set (Square d))
    (hM : Bornology.IsBounded M) (hne : M.Nonempty) (n : ℕ) :
    familyGrowth (closure M) n = familyGrowth M n := by
  exact complex_closure_growth M hM hne n

theorem paper_complex_closure_radius {d : ℕ} (M : Set (Square d))
    (hM : Bornology.IsBounded M) (hne : M.Nonempty) :
    jointSpectralRadius (closure M) = jointSpectralRadius M := by
  exact complex_closure_radius M hM hne

theorem paper_complex_bounded_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : Bornology.IsBounded M) (hne : M.Nonempty) :
    Tendsto (rootGrowth M) atTop (𝓝 (jointSpectralRadius M)) := by
  exact complex_bounded_root_limit hd M hM hne

theorem paper_real_bounded_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (RealSquare d))
    (hM : Bornology.IsBounded M) (hne : M.Nonempty) :
    Tendsto (realRootGrowth M) atTop (𝓝 (realRadius M)) := by
  exact real_bounded_root_limit hd M hM hne

theorem paper_complex_bounded_positive_radius_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (hr : 0 < jointSpectralRadius M) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) *
      (jointSpectralRadius M)^((n : ℤ)-(d : ℤ)+1) := by
  exact complex_bounded_positive_radius_growth hd M hM hne L hL hML hr n hn

theorem paper_real_bounded_positive_radius_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (hr : 0 < realRadius M) (n : ℕ) (hn : 1 ≤ n) :
    realFamilyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) *
      (realRadius M)^((n : ℤ)-(d : ℤ)+1) := by
  exact real_bounded_positive_radius_growth hd M hM hne L hL hML hr n hn

theorem paper_complex_bounded_zero_radius_nilpotent {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hr : jointSpectralRadius M = 0)
    (w : List (Square d)) (hw : WordIn M w) (hlen : d ≤ w.length) : matrixProduct w = 0 := by
  exact complex_bounded_zero_radius_nilpotent hd M hM hne L hL hML hr w hw hlen

theorem paper_real_bounded_zero_radius_nilpotent {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hr : realRadius M = 0)
    (w : List (RealSquare d)) (hw : ∀ A ∈ w, A ∈ M) (hlen : d ≤ w.length) :
    realMatrixProduct w = 0 := by
  exact real_bounded_zero_radius_nilpotent hd M hM hne L hL hML hr w hw hlen

theorem paper_theta_one : theta 1 = 1 := by
  exact theta_one

theorem paper_theta_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    theta d = (d : ℝ)*(2*Real.exp 1*(d : ℝ)^2/((d : ℝ)-1))^(d-1) := by
  exact theta_of_two_le hd

theorem paper_complex_bounded_radius_one_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (hr : jointSpectralRadius M = 1) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) := by
  exact complex_bounded_radius_one_growth hd M hM hne L hL hML hr n hn

theorem paper_real_bounded_radius_one_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (hr : realRadius M = 1) (n : ℕ) (hn : 1 ≤ n) :
    realFamilyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) := by
  exact real_bounded_radius_one_growth hd M hM hne L hL hML hr n hn

theorem paper_complex_bounded_comparison {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    familyGrowth M n ≤ (d : ℝ)*s^(d-1) *
      (jointSpectralRadius M + 2*(d : ℝ)^2*L/s)^n := by
  exact complex_bounded_comparison hd M hM hne L hL hML s hs n

theorem paper_real_bounded_comparison {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    realFamilyGrowth M n ≤ (d : ℝ)*s^(d-1) *
      (realRadius M + 2*(d : ℝ)^2*L/s)^n := by
  exact real_bounded_comparison hd M hM hne L hL hML s hs n

#print axioms paper_complex_closure_growth
#print axioms paper_complex_closure_radius
#print axioms paper_complex_bounded_root_limit
#print axioms paper_real_bounded_root_limit
#print axioms paper_complex_bounded_positive_radius_growth
#print axioms paper_real_bounded_positive_radius_growth
#print axioms paper_complex_bounded_zero_radius_nilpotent
#print axioms paper_real_bounded_zero_radius_nilpotent
#print axioms paper_theta_one
#print axioms paper_theta_of_two_le
#print axioms paper_complex_bounded_radius_one_growth
#print axioms paper_real_bounded_radius_one_growth
#print axioms paper_complex_bounded_comparison
#print axioms paper_real_bounded_comparison

end NLA.MF05.Paper
