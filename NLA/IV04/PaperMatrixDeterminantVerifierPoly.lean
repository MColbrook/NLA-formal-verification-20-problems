module

public import NLA.IV04.PaperMatrixDeterminantVerifierDefinitions
public import NLA.IV04.PaperDenseContinuantDeterminant
public import NLA.IV04.PaperStrictMatrixValidation
public import NLA.IV04.PaperMatrixDenseSupport
public import NLA.IV04.PaperBudgetedPowerPoly
public import NLA.IV04.PaperScaledThreshold
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem binary_input_cobham_comp {arity : ℕ} {f : List Bool → List Bool → List Bool}
    {left right : (Fin arity → List Bool) → List Bool}
    (hf : Cobham fun v : Fin 2 → List Bool => f (v 0) (v 1))
    (hl : Cobham left) (hr : Cobham right) : Cobham fun v => f (left v) (right v) :=
  (Cobham.comp₂ hf hl hr).of_eq fun _ => rfl

theorem matrix_determinant_threshold_fields_cobham :
    Cobham fun v : Fin 2 → List Bool => matrixDeterminantThresholdFields (v 0) (v 1) := by
  have hs := Cobham.proj (0 : Fin 2)
  have hd := Cobham.fstBlockFn (Cobham.sndBlockFn hs)
  have hD := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn hs))
  have hb := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn hs)))
  have hw := Cobham.fstBlockFn hb
  have ht := Cobham.fstBlockFn (Cobham.fstBlockFn (Cobham.sndBlockFn hb))
  have hdet := unary_input_cobham_comp polynomial_dense_integer_determinant_cobham
    (input_pair_cobham_comp hd hw)
  simpa only [matrixDeterminantThresholdFields] using input_pair_cobham_comp hdet
    (input_pair_cobham_comp ht (input_pair_cobham_comp hD (Cobham.proj (1 : Fin 2))))

theorem matrix_determinant_threshold_argument_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixDeterminantThresholdArgument (v 0) := by
  have hp := unary_input_cobham_comp encoded_matrix_denominator_power_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1)))
  simpa only [matrixDeterminantThresholdArgument] using binary_input_cobham_comp
    matrix_determinant_threshold_fields_cobham encoded_ordered_matrix_vertex_selection_cobham hp

theorem encoded_matrix_determinant_verifier_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixDeterminantVerifier (v 0) := by
  have hs := Cobham.comp encoded_matrix_dense_support_flag_cobham
    fun _ : Fin 1 => Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have ht := Cobham.comp encoded_scaled_determinant_threshold_cobham
    fun _ : Fin 1 => matrix_determinant_threshold_argument_cobham
  exact (Cobham.andFn encoded_strict_matrix_selection_flag_cobham (Cobham.andFn hs ht)).of_eq fun _ => rfl

theorem encoded_matrix_determinant_verifier_mem_fp : encodedMatrixDeterminantVerifier ∈ FP :=
  CobhamFP_subset_FP encoded_matrix_determinant_verifier_cobham

#print axioms encoded_matrix_determinant_verifier_mem_fp
end IV04.Paper.Computational