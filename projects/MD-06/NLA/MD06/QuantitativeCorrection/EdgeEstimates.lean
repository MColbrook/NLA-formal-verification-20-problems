module

public import NLA.MD06.QuantitativeCorrection.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open scoped BigOperators

theorem actual_euclidean_edge_difference_bound {n : ℕ} (h : Configuration n)
    (i j : Fin n) (hij : i ≠ j) : |h i-h j| ≤ Real.sqrt 2 * ‖h‖ := by
  classical
  have hs : (h i)^2+(h j)^2 ≤ ‖h‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have ht := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i,j} : Finset (Fin n)))
      (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) (_ : a ∉ ({i,j} : Finset (Fin n))) => sq_nonneg (h a))
    simpa only [Finset.sum_pair hij] using ht
  have hr : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : |h i-h j|^2 ≤ (Real.sqrt 2 * ‖h‖)^2 := by
    rw [sq_abs,mul_pow,hr]
    nlinarith [sq_nonneg (h i+h j)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

theorem actual_edge_cosine_perturbation {n : ℕ} (phi h : Configuration n)
    (i j : Fin n) (hij : i ≠ j) :
    Real.cos (phi i-phi j)-Real.sqrt 2*‖h‖ ≤
      Real.cos ((phi i+h i)-(phi j+h j)) := by
  have hc := Real.abs_cos_sub_cos_le (phi i-phi j) ((phi i+h i)-(phi j+h j))
  have he : (phi i-phi j)-((phi i+h i)-(phi j+h j)) = -(h i-h j) := by ring
  rw [he,abs_neg] at hc
  have hb := actual_euclidean_edge_difference_bound h i j hij
  have hl := le_abs_self (Real.cos (phi i-phi j)-Real.cos ((phi i+h i)-(phi j+h j)))
  linarith

theorem actual_correction_ball_edge_cosines {n : ℕ} (G : SimpleGraph (Fin n))
    (phi h : Configuration n) (c : ℝ)
    (hball : ‖h‖ ≤ c/(2*Real.sqrt 2))
    (hcos : ∀ i j, G.Adj i j → c ≤ Real.cos (phi i-phi j)) :
    ∀ i j, G.Adj i j → c/2 ≤ Real.cos ((phi i+h i)-(phi j+h j)) := by
  intro i j hij
  have ht := actual_edge_cosine_perturbation phi h i j (G.ne_of_adj hij)
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr : Real.sqrt 2*‖h‖ ≤ c/2 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt (2 : ℝ))).mp hball
    nlinarith
  linarith [hcos i j hij]

#print axioms actual_euclidean_edge_difference_bound
#print axioms actual_edge_cosine_perturbation
#print axioms actual_correction_ball_edge_cosines
end Reference.MD06Correction
