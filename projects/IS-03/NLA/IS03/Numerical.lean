module

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The single numerical sign needed for the seventh-moment contradiction.
-/
public import NLA.IS03.Definitions
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace NLA.IS03

/-- Kernel-certified singleton rational sign; no interval search is needed. -/
theorem numerical_negative_moment : (-8593/823543 : ℝ) < 0 := by
  norm_num

theorem negative_moment_proved :
    traceMoments 6 = (-8593/823543 : ℝ) ∧ traceMoments 6 < 0 := by
  exact ⟨rfl, numerical_negative_moment⟩

#print axioms numerical_negative_moment
end NLA.IS03
