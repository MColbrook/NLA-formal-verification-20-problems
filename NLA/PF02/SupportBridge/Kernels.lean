module

public import NLA.PF02.SupportBridge.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.PF02Support
open Matrix
open scoped BigOperators MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem lin_zero_iff (A : Mat n) (x : Vector n) :
    lin A x = 0 ↔ A *ᵥ x.ofLp = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun v : Vector n => v.ofLp) h
    change A *ᵥ x.ofLp = 0 at h'
    exact h'
  · intro h
    change WithLp.toLp 2 (A *ᵥ x.ofLp) = 0
    rw [h]
    rfl

omit [DecidableEq n] in
theorem sum_mulVec_zero_iff {ι : Type*} [Fintype ι]
    (B : ι → Mat n) (hB : ∀ j, (B j).PosSemidef) (x : n → ℝ) :
    (∑ j, B j) *ᵥ x = 0 ↔ ∀ j, B j *ᵥ x = 0 := by
  classical
  constructor
  · intro h
    have hsum : ∑ j, (star x ⬝ᵥ (B j *ᵥ x)) = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, h]
      simp
    have heach : ∀ j, star x ⬝ᵥ (B j *ᵥ x) = 0 := by
      simpa only [Finset.mem_univ, forall_true_left] using
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hB j).dotProduct_mulVec_nonneg x)).mp hsum
    intro j
    exact ((hB j).dotProduct_mulVec_zero_iff (x := x)).mp (heach j)
  · intro h
    rw [Matrix.sum_mulVec]
    simp only [h, Finset.sum_const_zero]

omit [Fintype n] [DecidableEq n] in
theorem psd_sum {ι : Type*} [Fintype ι]
    (B : ι → Mat n) (hB : ∀ j, (B j).PosSemidef) : (∑ j, B j).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun j _ => hB j)

theorem kernel_sum_eq_common_kernel {ι : Type*} [Fintype ι]
    (B : ι → Mat n) (hB : ∀ j, (B j).PosSemidef) :
    kernel (∑ j, B j) = ⨅ j, kernel (B j) := by
  ext x
  simp only [kernel, LinearMap.mem_ker, Submodule.mem_iInf]
  simp only [lin_zero_iff, sum_mulVec_zero_iff B hB]

theorem kernel_sum_le_each {ι : Type*} [Fintype ι]
    (B : ι → Mat n) (hB : ∀ j, (B j).PosSemidef) (j : ι) :
    kernel (∑ a, B a) ≤ kernel (B j) := by
  rw [kernel_sum_eq_common_kernel B hB]
  exact iInf_le _ j

#print axioms lin_zero_iff
#print axioms sum_mulVec_zero_iff
#print axioms psd_sum
#print axioms kernel_sum_eq_common_kernel
#print axioms kernel_sum_le_each
end Reference.PF02Support

