module

public import NLA.PF02.GlobalOrientation.Definitions
public import Mathlib.Topology.Instances.Matrix

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper
open scoped BigOperators

theorem reflection_mask_symm {α : Type*} [DecidableEq α] (i j a b : α) :
    reflectionMask i j b a = reflectionMask i j a b := by
  simp [reflectionMask, and_comm, or_comm]

theorem reflection_mask_mul_reverse {α : Type*} [DecidableEq α] (i j a b : α) :
    reflectionMask i j a b * reflectionMask i j b a = 1 := by
  rw [reflection_mask_symm]
  unfold reflectionMask
  split_ifs <;> norm_num

theorem entry_reflection_trace {α : Type*} [Fintype α] [DecidableEq α]
    (i j : α) (A B : Matrix α α ℝ) :
    trace (entryReflection i j A * entryReflection i j B) = trace (A * B) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, entryReflection]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    reflectionMask i j a b * A a b * (reflectionMask i j b a * B b a) =
        (reflectionMask i j a b * reflectionMask i j b a) * (A a b * B b a) := by ring
    _ = A a b * B b a := by rw [reflection_mask_mul_reverse, one_mul]

theorem entry_reflection_involution {α : Type*} [DecidableEq α]
    (i j : α) (A : Matrix α α ℝ) : entryReflection i j (entryReflection i j A) = A := by
  ext a b
  have h := reflection_mask_mul_reverse i j a b
  rw [reflection_mask_symm i j a b] at h
  simp only [entryReflection, ← mul_assoc, h, one_mul]

theorem entry_reflection_add {α : Type*} [DecidableEq α]
    (i j : α) (A B : Matrix α α ℝ) :
    entryReflection i j (A+B) = entryReflection i j A + entryReflection i j B := by
  ext a b
  simp [entryReflection, mul_add]

theorem entry_reflection_smul {α : Type*} [DecidableEq α]
    (i j : α) (c : ℝ) (A : Matrix α α ℝ) :
    entryReflection i j (c • A) = c • entryReflection i j A := by
  ext a b
  simp [entryReflection, mul_left_comm]

theorem entry_reflection_one {α : Type*} [DecidableEq α]
    (i j : α) (hij : i ≠ j) : entryReflection i j (1 : Matrix α α ℝ) = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    have hf : ¬ ((a = i ∧ a = j) ∨ (a = j ∧ a = i)) := by
      rintro (⟨hai,haj⟩ | ⟨haj,hai⟩) <;> exact hij (hai.symm.trans haj)
    simp [entryReflection, reflectionMask, hf]
  · simp [entryReflection, hab]

theorem entry_reflection_shift_trace {α : Type*} [Fintype α] [DecidableEq α]
    (i j : α) (hij : i ≠ j) (A B : Matrix α α ℝ) (η : ℝ) :
    trace ((entryReflection i j A + η • 1) * (entryReflection i j B + η • 1)) =
      trace ((A + η • 1) * (B + η • 1)) := by
  have h := entry_reflection_trace i j (A+η•1) (B+η•1)
  simpa only [entry_reflection_add, entry_reflection_smul, entry_reflection_one i j hij] using h

#print axioms reflection_mask_symm
#print axioms reflection_mask_mul_reverse
#print axioms entry_reflection_trace
#print axioms entry_reflection_involution
#print axioms entry_reflection_add
#print axioms entry_reflection_smul
#print axioms entry_reflection_one
#print axioms entry_reflection_shift_trace
end Reference.PF02GlobalOrientation
