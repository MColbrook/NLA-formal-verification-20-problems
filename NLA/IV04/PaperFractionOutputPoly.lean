module

public import NLA.IV04.PaperFractionOutputDefinitions
public import NLA.IV04.PaperCanonicalWord
public import NLA.IV04.PaperSATLiteralDigitsPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
theorem polynomial_fraction_output_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialFractionOutput (v 0) := by
  have hn := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hd := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hnc := sat_literal_cobham_unary canonicalWordCode canonical_word_code_cobham
    (fun v : Fin 1 → List Bool => (pairFst (v 0)).tail) (Cobham.tailFn hn)
  have hdc := sat_literal_cobham_unary canonicalWordCode canonical_word_code_cobham
    (fun v : Fin 1 → List Bool => pairSnd (v 0)) hd
  have hf := Cobham.appendFn hnc hdc
  have ht := sat_literal_cobham_unary (fun bits => true :: bits) (Cobham.bit true)
    (fun v : Fin 1 → List Bool => canonicalWordCode (pairFst (v 0)).tail ++ canonicalWordCode (pairSnd (v 0))) hf
  have hz := sat_literal_cobham_unary (fun bits => false :: bits) (Cobham.bit false)
    (fun v : Fin 1 → List Bool => canonicalWordCode (pairFst (v 0)).tail ++ canonicalWordCode (pairSnd (v 0))) hf
  exact (Cobham.iteFn (Cobham.headFlagFn hn) ht hz).of_eq fun _ => rfl
theorem polynomial_fraction_output_mem_fp : polynomialFractionOutput ∈ FP :=
  CobhamFP_subset_FP polynomial_fraction_output_cobham
#print axioms polynomial_fraction_output_mem_fp
end IV04.Paper.Computational
