module

public import NLA.MF12.ExactTensor.Norm

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace NLA.MF12.ExactTensor

theorem actual_tensor_word_norm {d e : ℕ} (A P : Square d) (J : Square e)
    (w : List Bool) :
    spectralNorm (binaryProduct (tensor A J) (tensor P J) w) =
      spectralNorm (binaryProduct A P w) * spectralNorm (J^w.length) := by
  rw [tensor_word_identity, actual_tensor_norm]

theorem actual_tensor_pair_growth {d e : ℕ} (A P : Square d) (J : Square e) (n : ℕ) :
    familyGrowth (pairFamily (tensor A J) (tensor P J)) n =
      familyGrowth (pairFamily A P) n * spectralNorm (J^n) := by
  apply le_antisymm
  · apply familyGrowth_le_of_binary
    intro w hwn
    rw [actual_tensor_word_norm, hwn]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [hwn] using binaryProduct_le_familyGrowth A P w)
      (spectralNorm_nonneg _)
  · have hmax := (wordNorms_nonempty (pairFamily A P) (by simp [pairFamily]) n).csSup_mem
      (wordNorms_finite (pairFamily A P) n)
    rw [pair_word_norms] at hmax
    obtain ⟨w, hwn, heq⟩ := hmax
    have hg : familyGrowth (pairFamily A P) n = spectralNorm (binaryProduct A P w) := by
      unfold familyGrowth
      rw [pair_word_norms]
      exact heq
    calc
      familyGrowth (pairFamily A P) n * spectralNorm (J^n) =
          spectralNorm (binaryProduct A P w) * spectralNorm (J^w.length) := by rw [hg,hwn]
      _ = spectralNorm (binaryProduct (tensor A J) (tensor P J) w) :=
        (actual_tensor_word_norm A P J w).symm
      _ ≤ familyGrowth (pairFamily (tensor A J) (tensor P J)) n := by
        simpa only [hwn] using binaryProduct_le_familyGrowth (tensor A J) (tensor P J) w

theorem actual_lifted_growth (α : ℝ) (m n : ℕ) :
    familyGrowth (pairFamily (liftedA α m) (liftedP m)) n =
      familyGrowth (pairFamily (fractionalMatrix α) resetMatrix) n *
        spectralNorm (jordanMatrix m ^ n) :=
  actual_tensor_pair_growth (fractionalMatrix α) resetMatrix (jordanMatrix m) n

#print axioms actual_tensor_pair_growth
#print axioms actual_lifted_growth

end NLA.MF12.ExactTensor
