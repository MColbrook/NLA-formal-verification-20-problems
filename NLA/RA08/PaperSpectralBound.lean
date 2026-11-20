module

public import NLA.RA08.PaperMatrixMinorant
public import NLA.RA08.Proof

@[expose] public section

set_option autoImplicit false
open scoped MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA08.Paper

theorem paper_functional_rayleigh_lower :
    26 * witnessT * (1 + (334583 / 15769728 : ℝ)) ≤
      witnessVector ⬝ᵥ ((functionalCalculus witnessFunction witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) *ᵥ witnessVector) := by
  have h := paperMinorant_matrix_le
  change (functionalCalculus witnessFunction witnessMatrix -
    paperMinorantMatrix witnessMatrix).PosSemidef at h
  have hq := h.dotProduct_mulVec_nonneg witnessVector
  have hc := paper_minorant_quadratic
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at hq hc ⊢
  linarith

theorem paper_spectral_norm_lower :
    witnessT * (1 + (334583 / 15769728 : ℝ)) ≤
      spectralNorm (functionalCalculus witnessFunction witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) := by
  have hq := operator_rayleigh_bound_proved
    (functionalCalculus witnessFunction witnessMatrix -
      functionalCalculus witnessFunction witnessApproximation) witnessVector
  rw [witness_vector_length] at hq
  have hl := paper_functional_rayleigh_lower
  have ha := le_abs_self (witnessVector ⬝ᵥ
    ((functionalCalculus witnessFunction witnessMatrix -
      functionalCalculus witnessFunction witnessApproximation) *ᵥ witnessVector))
  linarith

theorem paper_spectral_ratio (dA : OrderedSpectralData witnessMatrix) :
    1 + (334583 / 15769728 : ℝ) ≤
      spectralNorm (functionalCalculus witnessFunction witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) /
      spectralNorm (functionalCalculus witnessFunction witnessMatrix -
        functionTruncation dA witnessFunction 3) := by
  obtain ⟨dAhat⟩ := orderedSpectral_exists_proved witnessApproximation witnessApproximation_psd
  obtain ⟨_, _, _, _, _, hf⟩ := witness_tail_data_proved dA dAhat
  rw [hf]
  apply (le_div_iff₀ witnessT_pos).mpr
  simpa [mul_comm] using paper_spectral_norm_lower

#print axioms paper_spectral_ratio
end NLA.RA08.Paper
