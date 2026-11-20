module

public import NLA.RA09.Paper.Rank
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Tactic

@[expose] public section

/-! Actual diagonal matrices used by the unordered sharpness example. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder
namespace NLA.RA09.Paper

theorem functionalCalculus_diagonal {n : ℕ} (v : Fin n → ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    functionalCalculus f (Matrix.diagonal v) = Matrix.diagonal (fun i => f (v i)) := by
  let ev : C(spectrum ℝ (Matrix.diagonal v), ℝ) →⋆ₐ[ℝ] (Fin n → ℝ) := {
    toFun := fun g i => g ⟨v i, (spectrum_diagonal v).symm ▸ Set.mem_range_self i⟩
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl
    map_star' := fun _ => rfl }
  let φ := (realDiagonalStarAlgHom n).comp ev
  have hfinite : (spectrum ℝ (Matrix.diagonal v)).Finite := by
    rw [spectrum_diagonal]
    exact Set.finite_range v
  letI : Fintype (spectrum ℝ (Matrix.diagonal v)) := hfinite.fintype
  haveI : FiniteDimensional ℝ C(spectrum ℝ (Matrix.diagonal v), ℝ) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap ℝ (M := ℝ)) DFunLike.coe_injective
  have hφ : Continuous φ := φ.toLinearMap.continuous_of_finiteDimensional
  have hdiag : IsSelfAdjoint (Matrix.diagonal v) := by
    change (Matrix.diagonal v).conjTranspose = Matrix.diagonal v
    simp
  have hid : φ (.restrict (spectrum ℝ (Matrix.diagonal v)) (.id ℝ)) = Matrix.diagonal v := rfl
  have heq := cfcHom_eq_of_continuous_of_map_id hdiag φ hφ hid
  unfold functionalCalculus
  rw [cfc_apply f _ hdiag hf.continuousOn, heq]
  rfl

theorem functionTruncation_eq_cfc_of_rank_le {n : ℕ} {B : RealMatrix n}
    (d : OrderedSpectralData B) (k : ℕ) (hB : B.rank ≤ k)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) :
    functionTruncation d f k = functionalCalculus f B := by
  rw [selected_cfc_eq]
  apply congrArg (spectralCombination d)
  funext i
  by_cases hi : i.val < k
  · simp [hi]
  · simp [hi, eigenvalue_zero_of_rank_le d k hB i (Nat.le_of_not_gt hi), hf0]

def sharpA (N : ℕ) : RealMatrix (N+2) :=
  Matrix.diagonal (fun i => if i = Fin.last (N+1) then 0 else 1)

def sharpB (N : ℕ) (b : ℝ) : RealMatrix (N+2) :=
  Matrix.diagonal (fun i => if i = Fin.last (N+1) then b else 0)

def sharpDataA (N : ℕ) : OrderedSpectralData (sharpA N) where
  eigenvalues := fun i => if i = Fin.last (N+1) then 0 else 1
  orthogonal := 1
  decreasing := by
    intro i j hij
    dsimp
    split_ifs with hj hi hi
    · norm_num
    · norm_num
    · have : j = Fin.last (N+1) := by
        apply Fin.ext
        have h := (Fin.le_iff_val_le_val.mp hij)
        simp only [hi, Fin.val_last] at h
        exact congrArg Fin.val (le_antisymm j.le_last (show Fin.last (N+1) ≤ j from hi ▸ hij))
      contradiction
    · norm_num
  nonnegative := by intro i; split_ifs <;> norm_num
  reconstruct := by simp [sharpA]

theorem sharpA_psd (N : ℕ) : (sharpA N).PosSemidef :=
  (orderedSpectral_semantics_proved (sharpDataA N)).1

theorem sharpB_psd (N : ℕ) (b : ℝ) (hb : 0 ≤ b) : (sharpB N b).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  change 0 ≤ if i = Fin.last (N+1) then b else 0
  split_ifs <;> positivity

theorem sharpB_rank (N : ℕ) (b : ℝ) : (sharpB N b).rank ≤ 1 := by
  rw [sharpB, Matrix.rank_diagonal]
  have hinj : Function.Injective
      (fun (_ : {i : Fin (N+2) // (if i = Fin.last (N+1) then b else 0) ≠ 0}) =>
        (0 : Fin 1)) := by
    intro i j _
    apply Subtype.ext
    have hi : i.val = Fin.last (N+1) := by
      by_contra hi
      exact i.property (by simp [hi])
    have hj : j.val = Fin.last (N+1) := by
      by_contra hj
      exact j.property (by simp [hj])
    exact hi.trans hj.symm
  simpa using Fintype.card_le_of_injective _ hinj

theorem sharpA_cutoff (N : ℕ) (hN : 1 ≤ N) :
    (sharpDataA N).eigenvalues ⟨1, by omega⟩ = 1 := by
  simp only [sharpDataA]
  split_ifs with h
  · have := congrArg Fin.val h
    simp at this
    omega
  · rfl

theorem sharpA_tail (N : ℕ) : spectralTail (sharpDataA N) 1 = N := by
  simp only [spectralTail, sharpDataA, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.not_succ_le_zero, ↓reduceIte, zero_add,
    Fin.val_succ, Nat.succ_le_succ_iff, Nat.zero_le]
  have heq (i : Fin (N+1)) : i.succ = Fin.last (N+1) ↔ i = Fin.last N := by
    constructor <;> intro h <;> apply Fin.ext <;> have h' := congrArg Fin.val h <;>
      simp only [Fin.val_succ, Fin.val_last] at h' ⊢ <;> omega
  simp_rw [heq]
  rw [Fin.sum_univ_castSucc]
  simp

theorem sharpA_function_tail (N : ℕ) (f : ℝ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    functionTail (sharpDataA N) f 1 = N := by
  have h : functionTail (sharpDataA N) f 1 = spectralTail (sharpDataA N) 1 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [sharpDataA]
    split_ifs <;> simp [hf0, hf1]
  rw [h, sharpA_tail]

theorem sharp_input_error (N : ℕ) (b : ℝ) :
    frobeniusSquared (sharpA N - sharpB N b) = N+1+b^2 := by
  rw [sharpA, sharpB, Matrix.diagonal_sub, frobeniusSquared_diagonal]
  rw [Fin.sum_univ_castSucc]
  simp

theorem sharp_output_error (N : ℕ) (b : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (dB : OrderedSpectralData (sharpB N b)) :
    frobeniusSquared (functionalCalculus f (sharpA N) - functionTruncation dB f 1) =
      N+1+(f b)^2 := by
  rw [functionTruncation_eq_cfc_of_rank_le dB 1 (sharpB_rank N b) f hf0]
  rw [sharpA, sharpB, functionalCalculus_diagonal _ f hf,
    functionalCalculus_diagonal _ f hf, Matrix.diagonal_sub, frobeniusSquared_diagonal]
  rw [Fin.sum_univ_castSucc]
  simp [hf0, hf1]

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_eq_sqrt {n : ℕ} (M : RealMatrix n) :
    frobeniusNorm M = Real.sqrt (frobeniusSquared M) := by
  rw [frobeniusSquared_norm]
  exact (Real.sqrt_sq (norm_nonneg M)).symm

theorem sharp_norm_input (N : ℕ) (hN : 0 < N) (b : ℝ) :
    frobeniusNorm (sharpA N - sharpB N b) / Real.sqrt (spectralTail (sharpDataA N) 1) =
      Real.sqrt (1+(1+b^2)/(N : ℝ)) := by
  rw [frobeniusNorm_eq_sqrt, sharp_input_error, sharpA_tail, ← Real.sqrt_div (by positivity)]
  congr 1
  have : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp
  <;> ring

theorem sharp_norm_output (N : ℕ) (hN : 0 < N) (b : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (dB : OrderedSpectralData (sharpB N b)) :
    frobeniusNorm (functionalCalculus f (sharpA N) - functionTruncation dB f 1) /
        Real.sqrt (functionTail (sharpDataA N) f 1) =
      Real.sqrt (1+(1+(f b)^2)/(N : ℝ)) := by
  rw [frobeniusNorm_eq_sqrt, sharp_output_error N b f hf hf0 hf1 dB,
    sharpA_function_tail N f hf0 hf1, ← Real.sqrt_div (by positivity)]
  congr 1
  have : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp
  <;> ring

#print axioms sharp_output_error

end NLA.RA09.Paper
