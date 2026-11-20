module

public import NLA.IV04.PaperBinaryBounds
public import Mathlib.Data.Rat.Lemmas

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper

/-- Reducing an actual integer fraction cannot increase either payload. -/
theorem reduced_fraction_payload (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((a : ℚ)/(b : ℚ)).num.natAbs ≤ a.natAbs ∧
    ((a : ℚ)/(b : ℚ)).den ≤ b := by
  have hbz : (b : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  obtain ⟨k,hnum,hden⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hbz
  have hden' : (b : ℤ) = k*(((a : ℚ)/(b : ℚ)).den : ℤ) := by
    simpa using hden
  have hnum' : a = k*((a : ℚ)/(b : ℚ)).num := by simpa using hnum
  have hq : (0 : ℤ) < ((a : ℚ)/(b : ℚ)).den := by
    exact_mod_cast ((a : ℚ)/(b : ℚ)).pos
  have hbp : (0 : ℤ) < b := by exact_mod_cast hb
  have hk : 1 ≤ k := by nlinarith
  have hka : 1 ≤ k.natAbs := by
    have hk0 : k ≠ 0 := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hk0)
  constructor
  · have heq := congrArg Int.natAbs hnum'
    rw [Int.natAbs_mul] at heq
    calc ((a : ℚ)/(b : ℚ)).num.natAbs = 1*((a : ℚ)/(b : ℚ)).num.natAbs := by simp
         _ ≤ k.natAbs*((a : ℚ)/(b : ℚ)).num.natAbs := Nat.mul_le_mul_right _ hka
         _ = a.natAbs := heq.symm
  · have hle : (((a : ℚ)/(b : ℚ)).den : ℤ) ≤ b := by nlinarith
    exact_mod_cast hle

namespace IntegerPartition

theorem cosine_scaled_fraction (P : IntegerPartition) (i : Fin P.m) :
    P.c i = ((P.squaredScale : ℚ)-(P.weight i : ℚ)^2)/
      ((P.squaredScale : ℚ)+(P.weight i : ℚ)^2) := by
  have hW : (P.total : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (total_pos P))
  dsimp [c,t,delta,squaredScale,denominatorScale]
  push_cast
  field_simp [hW]

theorem sine_scaled_fraction (P : IntegerPartition) (i : Fin P.m) :
    P.s i = (2*(P.weight i : ℚ)*P.denominatorScale)/
      ((P.squaredScale : ℚ)+(P.weight i : ℚ)^2) := by
  have hW : (P.total : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (total_pos P))
  dsimp [s,t,delta,squaredScale,denominatorScale]
  push_cast
  field_simp [hW]

theorem companion_diagonal_scaled_fraction (P : IntegerPartition) (i : Fin P.m) :
    -P.s i/P.c i = -(2*(P.weight i : ℚ)*P.denominatorScale)/
      ((P.squaredScale : ℚ)-(P.weight i : ℚ)^2) := by
  have hm : (P.squaredScale : ℚ)-(P.weight i : ℚ)^2 ≠ 0 := by
    have h : (P.weight i : ℚ)^2 < (P.squaredScale : ℚ) := by
      exact_mod_cast squared_weight_lt_scale P i
    exact ne_of_gt (sub_pos.mpr h)
  have hp : (P.squaredScale : ℚ)+(P.weight i : ℚ)^2 ≠ 0 := by
    have h : (0 : ℚ) < P.squaredScale := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (squared_weight_lt_scale P i))
    positivity
  rw [sine_scaled_fraction,cosine_scaled_fraction]
  field_simp [hm,hp]

theorem companion_beta_scaled_fraction (P : IntegerPartition) (i : Fin P.m) :
    -1/P.c i = -((P.squaredScale : ℚ)+(P.weight i : ℚ)^2)/
      ((P.squaredScale : ℚ)-(P.weight i : ℚ)^2) := by
  have hm : (P.squaredScale : ℚ)-(P.weight i : ℚ)^2 ≠ 0 := by
    have h : (P.weight i : ℚ)^2 < (P.squaredScale : ℚ) := by
      exact_mod_cast squared_weight_lt_scale P i
    exact ne_of_gt (sub_pos.mpr h)
  have hp : (P.squaredScale : ℚ)+(P.weight i : ℚ)^2 ≠ 0 := by
    have h : (0 : ℚ) < P.squaredScale := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (squared_weight_lt_scale P i))
    positivity
  rw [cosine_scaled_fraction]
  field_simp [hm,hp]

theorem threshold_scaled_fraction (P : IntegerPartition) :
    P.threshold = (2*(P.squaredScale : ℚ)-1)/(2*(P.squaredScale : ℚ)) := by
  have hW : (P.total : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (total_pos P))
  dsimp [threshold,delta,squaredScale,denominatorScale]
  push_cast
  field_simp [hW]

end IntegerPartition
end IV04.Paper
