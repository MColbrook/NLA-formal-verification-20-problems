module

public import NLA.MI21.Proof

@[expose] public section

set_option autoImplicit false
open scoped Classical
noncomputable section
namespace NLA.MI21.Paper

theorem rational_witness_entries (i r s : Fin 2) :
    (∃ q : ℚ, (q : ℂ) = witnessA i r s) ∧
    (∃ q : ℚ, (q : ℂ) = witnessB i r s) := by
  let C : Matrix (Fin 2) (Fin 2) ℚ := Matrix.diagonal ![12/37,21/29]
  let E : Matrix (Fin 2) (Fin 2) ℚ := Matrix.diagonal ![35/37,20/29]
  let S : Matrix (Fin 2) (Fin 2) ℚ := (1/17 : ℚ) • !![15,8;8,-15]
  let f : Matrix (Fin 2) (Fin 2) ℚ →+* Mat 2 := (Rat.castHom ℂ).mapMatrix
  have hC : f C = witnessC := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [f, C, witnessC, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  have hE : f E = witnessE := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [f, E, witnessE, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  have hS : f S = witnessS := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [f, S, witnessS, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply]
  have hA : ∃ Q : Matrix (Fin 2) (Fin 2) ℚ, f Q = witnessA i := by
    fin_cases i
    · exact ⟨C^2, by simp [map_pow, hC, witnessA]⟩
    · exact ⟨E^2, by simp [map_pow, hE, witnessA]⟩
  have hB : ∃ Q : Matrix (Fin 2) (Fin 2) ℚ, f Q = witnessB i := by
    fin_cases i
    · exact ⟨S*E^2*S, by simp [map_mul, map_pow, hS, hE, witnessB]⟩
    · exact ⟨S*C^2*S, by simp [map_mul, map_pow, hS, hC, witnessB]⟩
  obtain ⟨QA, hQA⟩ := hA
  obtain ⟨QB, hQB⟩ := hB
  exact ⟨⟨QA r s, congrArg (fun M : Mat 2 => M r s) hQA⟩,
    ⟨QB r s, congrArg (fun M : Mat 2 => M r s) hQB⟩⟩

#print axioms rational_witness_entries
end NLA.MI21.Paper
