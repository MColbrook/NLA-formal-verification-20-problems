module

public import NLA.RA09.Paper.SharpFamily
public import NLA.RA09.PaperDefinitions

@[expose] public section

/-! A concrete ordered witness with f(x)=x and positive excess. -/
set_option autoImplicit false
noncomputable section
open scoped MatrixOrder
namespace NLA.RA09.Paper

theorem identity_admissible : PaperAdmissibleFunction (fun x : ℝ => x) := by
  refine ⟨continuous_id.continuousOn, monotone_id.monotoneOn _, fun x hx => hx, ?_⟩
  intro x y hx hxy
  simp [ne_of_gt hx, ne_of_gt (hx.trans_le hxy)]

theorem ordered_sharpness (γ : ℝ) (hγ : γ < 1) :
    ∃ (A B : RealMatrix 3) (dA : OrderedSpectralData A) (dB : OrderedSpectralData B),
      B ≤ A ∧ B.rank ≤ 1 ∧ dA.eigenvalues ⟨1, by decide⟩ = 1 ∧
      frobeniusSquared (A-B) - spectralTail dA 1 = 1 ∧
      γ * (frobeniusSquared (A-B) - spectralTail dA 1) <
        frobeniusSquared (functionalCalculus (fun x : ℝ => x) A -
          functionTruncation dB (fun x : ℝ => x) 1) - functionTail dA (fun x : ℝ => x) 1 := by
  let dB := Classical.choice (orderedSpectral_exists_proved _ (sharpB_psd 1 0 le_rfl))
  refine ⟨sharpA 1, sharpB 1 0, sharpDataA 1, dB, ?_, sharpB_rank 1 0,
    sharpA_cutoff 1 le_rfl, ?_, ?_⟩
  · have hz : sharpB 1 0 = 0 := by simp [sharpB]
    rw [hz]
    exact (sharpA_psd 1).nonneg
  · rw [sharp_input_error, sharpA_tail]
    norm_num
  · rw [sharp_input_error, sharpA_tail,
      sharp_output_error 1 0 (fun x : ℝ => x) continuous_id rfl rfl dB,
      sharpA_function_tail 1 (fun x : ℝ => x) rfl rfl]
    simpa using hγ

#print axioms ordered_sharpness

end NLA.RA09.Paper
