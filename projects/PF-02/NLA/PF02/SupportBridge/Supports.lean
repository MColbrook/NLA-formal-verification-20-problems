module

public import NLA.PF02.SupportBridge.TraceZero
public import NLA.PF02.SupportBridge.Kernels

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.PF02Support
open Matrix
open scoped BigOperators MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem image_orthogonal_eq_kernel (A : Mat n) (hA : A.PosSemidef) :
    (image A)ᗮ = kernel A := by
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian).orthogonal_range

theorem kernel_orthogonal_eq_image (A : Mat n) (hA : A.PosSemidef) :
    (kernel A)ᗮ = image A := by
  rw [← image_orthogonal_eq_kernel A hA]
  exact (image A).orthogonal_orthogonal

theorem image_le_kernel_of_mul_zero (A B : Mat n) (h : A * B = 0) :
    image B ≤ kernel A := by
  rintro x ⟨y, rfl⟩
  change lin A (lin B y) = 0
  rw [lin_zero_iff]
  change A *ᵥ (B *ᵥ y.ofLp) = 0
  rw [Matrix.mulVec_mulVec, h]
  simp

theorem psd_trace_zero_supported_kernel (A B : Mat n) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (h : Matrix.trace (A * B) = 0) :
    SupportedOn A (kernel B) := by
  exact image_le_kernel_of_mul_zero B A (psd_trace_zero_reverse_mul_zero A B hA hB h)

theorem psd_trace_zero_orthogonal_ranges (A B : Mat n) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (h : Matrix.trace (A * B) = 0) :
    (image A) ⟂ (image B) := by
  rw [Submodule.isOrtho_iff_le, image_orthogonal_eq_kernel B hB]
  exact psd_trace_zero_supported_kernel A B hA hB h

theorem psd_family_each_supported_sum_image {ι : Type*} [Fintype ι]
    (B : ι → Mat n) (hB : ∀ j, (B j).PosSemidef) (j : ι) :
    SupportedOn (B j) (image (∑ a, B a)) := by
  change image (B j) ≤ image (∑ a, B a)
  rw [← kernel_orthogonal_eq_image (B j) (hB j),
      ← kernel_orthogonal_eq_image (∑ a, B a) (psd_sum B hB)]
  exact Submodule.orthogonal_le (kernel_sum_le_each B hB j)

theorem psd_trace_zero_family_supported_common_kernel {ι : Type*} [Fintype ι]
    (A : Mat n) (B : ι → Mat n) (hA : A.PosSemidef)
    (hB : ∀ j, (B j).PosSemidef) (h : ∀ j, Matrix.trace (A * B j) = 0) :
    SupportedOn A (kernel (∑ j, B j)) := by
  have hz : ∀ j, B j * A = 0 := fun j => psd_trace_zero_reverse_mul_zero A (B j) hA (hB j) (h j)
  apply image_le_kernel_of_mul_zero
  rw [Finset.sum_mul]
  simp only [hz, Finset.sum_const_zero]

theorem psd_trace_zero_block_supported {ι κ : Type*} [Fintype ι]
    (A : κ → Mat n) (B : ι → Mat n) (hA : ∀ i, (A i).PosSemidef)
    (hB : ∀ j, (B j).PosSemidef) (h : ∀ i j, Matrix.trace (A i * B j) = 0) :
    (∀ j, SupportedOn (B j) (image (∑ a, B a))) ∧
    (∀ i, SupportedOn (A i) (kernel (∑ j, B j))) := by
  exact ⟨psd_family_each_supported_sum_image B hB,
    fun i => psd_trace_zero_family_supported_common_kernel (A i) B (hA i) hB (h i)⟩

#print axioms image_orthogonal_eq_kernel
#print axioms kernel_orthogonal_eq_image
#print axioms image_le_kernel_of_mul_zero
#print axioms psd_trace_zero_supported_kernel
#print axioms psd_trace_zero_orthogonal_ranges
#print axioms psd_family_each_supported_sum_image
#print axioms psd_trace_zero_family_supported_common_kernel
#print axioms psd_trace_zero_block_supported
end Reference.PF02Support

