module

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The exact singleton gap in the rational Rayleigh certificate.
-/
public import NLA.RA08.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08

/-- A material kernel-reduced rational sign, without eigenvalue intervals. -/
theorem numerical_gap_positive_proved : 0 < witnessGap := by
  unfold witnessGap
  norm_num

#print axioms numerical_gap_positive_proved

end NLA.RA08
