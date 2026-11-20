module

public import NLA.IV04.PaperMatrixVerifierNPDefinitions
public import NLA.IV04.PaperMatrixDeterminantVerifierSemantics
public import NLA.IV04.Complexitylib.Classes.NP.Verifier.Linear
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem encoded_matrix_bounded_witness_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixBoundedWitnessFlag (v 0) := by
  have h0 := Cobham.proj (0 : Fin 1)
  have hx := Cobham.fstBlockFn h0
  have hy := Cobham.sndBlockFn h0
  have hcanonical := Cobham.eqFlag_mem (input_pair_cobham_comp hx hy) h0
  have hbudget := Cobham.lenLeFlag_mem (Cobham.comp (Cobham.bit false) fun _ : Fin 1 => hx) hy
  have haccept := Cobham.eqFlag_mem encoded_matrix_determinant_verifier_cobham (.const [true])
  exact (Cobham.andFn hcanonical (Cobham.andFn hbudget haccept)).of_eq fun _ => rfl

theorem encoded_matrix_bounded_witness_mem_fp : encodedMatrixBoundedWitnessFlag ∈ FP :=
  CobhamFP_subset_FP encoded_matrix_bounded_witness_cobham

theorem matrix_bounded_witness_flag_pair_language (input : List Bool) :
    encodedMatrixBoundedWitnessFlag input=[true] ↔ input ∈ pairLang matrixBoundedWitness := by
  rw [encodedMatrixBoundedWitnessFlag,
    Cobham.andBit_eq_true_iff (Cobham.eqFlag_flag _ _) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (Cobham.lenLeFlag_flag _ _) (Cobham.eqFlag_flag _ _)]
  simp only [Cobham.eqFlag_eq_true_iff,Cobham.lenLeFlag_eq_true_iff,List.length_cons]
  constructor
  · rintro ⟨he,hbudget,haccept⟩
    exact ⟨pairFst input,pairSnd input,he.symm,hbudget,by rw [he];exact haccept⟩
  · rintro ⟨matrix,choices,rfl,hbudget,haccept⟩
    simp only [pairFst_pair,pairSnd_pair]
    exact ⟨True.intro,hbudget,haccept⟩

theorem matrix_bool_fp_language {f : List Bool → List Bool} (hfp : f ∈ FP)
    {L : Language} (hflag : ∀ input, f input=[true] ∨ f input=[false])
    (hcorrect : ∀ input, f input=[true] ↔ input ∈ L) : L ∈ P := by
  obtain ⟨degree,tapes,machine,time,hmachine,htime⟩ := hfp
  apply Set.mem_iUnion.mpr
  refine ⟨degree,tapes,machine,time,?_,htime⟩
  intro input
  obtain ⟨state,steps,hsteps,hreaches,hhalted,hout⟩ := hmachine input
  refine ⟨state,steps,hsteps,hreaches,hhalted,?_,?_⟩
  · intro hin
    rw [(hcorrect input).mpr hin] at hout
    simpa [Γ.ofBool] using hout.1 0 (by simp)
  · intro houtside
    have hfalse : f input=[false] := (hflag input).resolve_left fun h => houtside ((hcorrect input).mp h)
    rw [hfalse] at hout
    simpa [Γ.ofBool] using hout.1 0 (by simp)

theorem matrix_bounded_pair_language_mem_p : pairLang matrixBoundedWitness ∈ P :=
  matrix_bool_fp_language encoded_matrix_bounded_witness_mem_fp
    (fun input => andBit_flag _ _) matrix_bounded_witness_flag_pair_language

theorem matrix_verifier_language_mem_np : matrixVerifierLanguage ∈ NP := by
  apply NP.mem_NP_of_linear_witness
    (R:=matrixBoundedWitness) (fun _ _ h => h.1) (fun _ => Iff.rfl)
  exact matrix_bounded_pair_language_mem_p

#print axioms matrix_verifier_language_mem_np
end IV04.Paper.Computational