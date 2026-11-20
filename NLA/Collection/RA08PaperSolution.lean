module

public import NLA.RA08.PaperNystrom
public import NLA.RA08.PaperSpectralBound

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped MatrixOrder
open Matrix
namespace NLA.RA08.Paper

theorem paper_spectral_witness :
    Nonempty (OrderedSpectralData witnessMatrix) ∧
    Function.Injective (fun x => paperOmega *ᵥ x) ∧
    IsUnit (paperOmega.transpose * witnessMatrix * paperOmega).det ∧
    witnessMatrix.PosDef ∧ witnessApproximation.PosSemidef ∧
    witnessApproximation ≤ witnessMatrix ∧
    nystrom witnessMatrix paperOmega = witnessApproximation := by
  exact ⟨orderedSpectral_exists_proved witnessMatrix witnessMatrix_psd,
    paper_sketch_injective, paper_gram_invertible, witnessMatrix_posDef,
    witnessApproximation_psd, witness_order, paper_nystrom_identity⟩

theorem paper_spectral_errors (dA : OrderedSpectralData witnessMatrix) :
    spectralNorm (witnessMatrix - witnessApproximation) = witnessT ∧
    spectralNorm (witnessMatrix - truncation dA 3) = witnessT ∧
    spectralNorm (functionalCalculus witnessFunction witnessMatrix -
      functionTruncation dA witnessFunction 3) = witnessT ∧
    1 + (334583 / 15769728 : ℝ) ≤
      spectralNorm (functionalCalculus witnessFunction witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) /
      spectralNorm (functionalCalculus witnessFunction witnessMatrix -
        functionTruncation dA witnessFunction 3) ∧
    (1 : ℝ) < 1 + (334583 / 15769728 : ℝ) := by
  obtain ⟨dAhat⟩ := orderedSpectral_exists_proved witnessApproximation witnessApproximation_psd
  obtain ⟨hres, _, _, _, ha, hf⟩ := witness_tail_data_proved dA dAhat
  exact ⟨hres, ha, hf, paper_spectral_ratio dA, by norm_num⟩

theorem paper_spectral_failure (C : ℝ) (dA : OrderedSpectralData witnessMatrix) :
    spectralNorm (witnessMatrix - witnessApproximation) ≤
      (1 + (0 : ℝ)) * spectralNorm (witnessMatrix - truncation dA 3) ∧
    ¬ (spectralNorm (functionalCalculus witnessFunction witnessMatrix -
          functionalCalculus witnessFunction witnessApproximation) ≤
        (1 + C * 0) * spectralNorm (functionalCalculus witnessFunction witnessMatrix -
          functionTruncation dA witnessFunction 3)) := by
  obtain ⟨dAhat⟩ := orderedSpectral_exists_proved witnessApproximation witnessApproximation_psd
  have hc := counterexample_proved dA dAhat
  rw [approximation_truncation dAhat, approximation_function_truncation dAhat] at hc
  simpa using hc

theorem paper_scalar_function :
    AdmissibleFunction witnessFunction ∧ witnessFunction 0 = 0 := by
  exact ⟨witnessFunction_admissible, by norm_num [witnessFunction]⟩

#print axioms paper_spectral_witness
#print axioms paper_spectral_errors
#print axioms paper_spectral_failure
#print axioms paper_scalar_function

end NLA.RA08.Paper
