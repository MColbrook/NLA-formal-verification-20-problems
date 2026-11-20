module

public import NLA.PF02.UniformPositiveOrientation.PerturbationDefinitions
public import NLA.PF02.GlobalOrientation.ReflectedWitness

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction
open scoped BigOperators MatrixOrder

theorem shifted_psd {p k : ℕ} (A : Fin p → Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i, (A i).PosSemidef) (η : ℝ) (hη : 0 ≤ η) (i : Fin p) :
    (shiftedFactors A η i).PosSemidef :=
  (hA i).add (Matrix.PosDef.one.posSemidef.smul hη)

theorem shifted_posDef {p k : ℕ} (A : Fin p → Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i, (A i).PosSemidef) (η : ℝ) (hη : 0 < η) (i : Fin p) :
    (shiftedFactors A η i).PosDef := by
  simpa only [shiftedFactors,add_comm] using (Matrix.PosDef.one.smul hη).add_posSemidef (hA i)

theorem actual_shifted_factorization (r : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    NLA.PF02.IsFactorization (perturbedBlockGram r η)
      (shiftedFactors (enumeratedFactor r) η,shiftedFactors (enumeratedFactor r) η) := by
  refine ⟨shifted_psd _ (enumerated_factorization r).1 η hη,
    shifted_psd _ (enumerated_factorization r).2.1 η hη,?_⟩
  intro i j
  rfl

theorem finite_reflected_entry_covariance (r : ℕ) (p : BlockIndex r) :
    finiteReflectedBlockFactor r p = entryReflection
      (finSumFinEquiv (Sum.inl (0 : Fin 3)) : Fin (3+r))
      (finSumFinEquiv (Sum.inl (1 : Fin 3)) : Fin (3+r)) (finiteBlockFactor r p) := by
  ext a b
  simp only [finiteReflectedBlockFactor,finiteBlockFactor,reflected_block_factor_eq,
    entryReflection,Matrix.submatrix_apply,reflectionMask,Equiv.symm_apply_eq]

theorem enumerated_reflected_entry_covariance (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    enumeratedReflectedFactor r i = entryReflection
      (finSumFinEquiv (Sum.inl (0 : Fin 3)) : Fin (3+r))
      (finSumFinEquiv (Sum.inl (1 : Fin 3)) : Fin (3+r)) (enumeratedFactor r i) :=
  finite_reflected_entry_covariance r _

theorem actual_shifted_reflected_factorization (r : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    NLA.PF02.IsFactorization (perturbedBlockGram r η)
      (shiftedFactors (enumeratedReflectedFactor r) η,shiftedFactors (enumeratedReflectedFactor r) η) := by
  refine ⟨shifted_psd _ (enumerated_reflected_factorization r).1 η hη,
    shifted_psd _ (enumerated_reflected_factorization r).2.1 η hη,?_⟩
  intro i j
  have hij : (finSumFinEquiv (Sum.inl (0 : Fin 3)) : Fin (3+r)) ≠
      (finSumFinEquiv (Sum.inl (1 : Fin 3)) : Fin (3+r)) := by
    intro h
    have hh := finSumFinEquiv.injective h
    simp at hh
  have h := entry_reflection_shift_trace _ _ hij (enumeratedFactor r i) (enumeratedFactor r j) η
  simpa only [shiftedFactors,enumerated_reflected_entry_covariance,
    perturbedBlockGram,Reference.PF02JointCompactness.perturbedGram] using h

#print axioms shifted_psd
#print axioms shifted_posDef
#print axioms actual_shifted_factorization
#print axioms finite_reflected_entry_covariance
#print axioms enumerated_reflected_entry_covariance
#print axioms actual_shifted_reflected_factorization
end Reference.PF02UniformPositiveOrientation
