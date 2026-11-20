module

public import NLA.RA09.SpectralOptimality.RealSelected
public import NLA.RA09.SpectralOptimality.ExampleDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder
namespace RootRA09SpectralOptimality
open NLA.RA09

theorem actual_branch_discriminant (d : ℝ) (hd : 1 ≤ d) :
    0 < 2*(d+1) ∧
      (-(2*d+1))^2-4*(2*(d+1))*d = 1-4*d*(d+1) ∧
      1-4*d*(d+1) < 0 := by
  refine ⟨by linarith, by ring, ?_⟩
  nlinarith [sq_nonneg (d-1)]

theorem sharp_identity_admissible : PaperAdmissibleFunction (fun x : ℝ => x) := by
  refine ⟨continuous_id.continuousOn, monotone_id.monotoneOn _, fun x hx => hx, ?_⟩
  intro x y hx hxy
  simp [ne_of_gt hx, ne_of_gt (hx.trans_le hxy)]

theorem actual_other_branch_signs (d : ℝ) (hd : 1 ≤ d) :
    (∀ z : ℝ, 1 ≤ z → z ≤ d → 0 ≤ (d-z)*(2*z+d-1)/z) ∧
      (∀ z : ℝ, d ≤ z → 0 ≤ (d-1)*(z-d)*(2*z-1)/z) := by
  constructor
  · intro z hz hzd
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hzd) (by linarith)) (by linarith)
  · intro z hz
    exact div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hd)
      (sub_nonneg.mpr hz)) (by linarith)) (by linarith)

theorem sharpB2_selected : functionTruncation sharpDataB2 (fun x : ℝ => x) 1 = sharpB2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [functionTruncation,spectralCombination,sharpDataB2,sharpB2,Matrix.diagonal_apply]

theorem actual_ordered_diagonal_sharpness (γ : ℝ) (hγ : γ < 1) :
    sharpA2.PosSemidef ∧ sharpB2.PosSemidef ∧ sharpB2 ≤ sharpA2 ∧ sharpB2.rank ≤ 1 ∧
      PaperAdmissibleFunction (fun x : ℝ => x) ∧ sharpDataA2.eigenvalues 1 = 1 ∧
      frobeniusSquared (sharpA2-sharpB2) - spectralTail sharpDataA2 1 = 1 ∧
      frobeniusSquared (functionalCalculus (fun x : ℝ => x) sharpA2 -
        functionTruncation sharpDataB2 (fun x : ℝ => x) 1) -
          functionTail sharpDataA2 (fun x : ℝ => x) 1 = 1 ∧
      γ * (frobeniusSquared (sharpA2-sharpB2) - spectralTail sharpDataA2 1) <
        frobeniusSquared (functionalCalculus (fun x : ℝ => x) sharpA2 -
          functionTruncation sharpDataB2 (fun x : ℝ => x) 1) -
            functionTail sharpDataA2 (fun x : ℝ => x) 1 := by
  have hA := (orderedSpectral_semantics_proved sharpDataA2).1
  have hB := (orderedSpectral_semantics_proved sharpDataB2).1
  have hid : sharpA2-sharpB2 = (1 : RealMatrix 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sharpA2,sharpB2,Matrix.diagonal_apply]
  have hle : sharpB2 ≤ sharpA2 := by
    apply sub_nonneg.mp
    rw [hid]
    exact Matrix.PosSemidef.one.nonneg
  have hr : sharpB2.rank ≤ 1 := by
    rw [← sharpB2_selected]
    exact (actual_real_selected_rank sharpDataB2 (fun x : ℝ => x) 1).2
  have he : frobeniusSquared (sharpA2-sharpB2)-spectralTail sharpDataA2 1 = 1 := by
    norm_num [frobeniusSquared,sharpA2,sharpB2,spectralTail,sharpDataA2,Finset.sum_filter,Fin.sum_univ_two,Matrix.diagonal_apply]
  have hf : functionalCalculus (fun x : ℝ => x) sharpA2 = sharpA2 := by
    rw [selected_cfc_eq sharpDataA2]
    exact sharpDataA2.reconstruct.symm
  have hfe : frobeniusSquared (functionalCalculus (fun x : ℝ => x) sharpA2-
      functionTruncation sharpDataB2 (fun x : ℝ => x) 1)-
        functionTail sharpDataA2 (fun x : ℝ => x) 1 = 1 := by
    rw [hf,sharpB2_selected]
    exact he
  refine ⟨hA,hB,hle,hr,sharp_identity_admissible,rfl,he,hfe,?_⟩
  simpa only [he,hfe,mul_one] using hγ

#print axioms actual_branch_discriminant
#print axioms actual_ordered_diagonal_sharpness
end RootRA09SpectralOptimality
