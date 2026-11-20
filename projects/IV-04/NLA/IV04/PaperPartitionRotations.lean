module

public import NLA.IV04.PaperPartitionDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace IV04.Paper
namespace IntegerPartition

theorem weight_le_total (P : IntegerPartition) (i : Fin P.m) :
    P.weight i ≤ P.total := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (P.weight j)) (Finset.mem_univ i)

theorem total_pos (P : IntegerPartition) : 0 < P.total := by
  let i : Fin P.m := ⟨0,P.nonempty⟩
  exact lt_of_lt_of_le (P.positive i) (weight_le_total P i)

theorem delta_pos (P : IntegerPartition) : 0 < P.delta := by
  have h : (0 : ℚ) < P.total := by exact_mod_cast total_pos P
  dsimp [delta]
  positivity

theorem delta_le_tenth (P : IntegerPartition) : P.delta ≤ 1/10 := by
  have h : (1 : ℚ) ≤ P.total := by exact_mod_cast total_pos P
  have hd : (0 : ℚ) < 10*(P.total : ℚ)^2 := by positivity
  rw [delta,div_le_iff₀ hd]
  nlinarith [sq_nonneg ((P.total : ℚ)-1)]

theorem t_pos (P : IntegerPartition) (i : Fin P.m) : 0 < P.t i := by
  have hw : (0 : ℚ) < P.weight i := by exact_mod_cast P.positive i
  exact mul_pos (delta_pos P) hw

theorem t_le_tenth (P : IntegerPartition) (i : Fin P.m) : P.t i ≤ 1/10 := by
  have hw : (P.weight i : ℚ) ≤ P.total := by exact_mod_cast weight_le_total P i
  have hW : (1 : ℚ) ≤ P.total := by exact_mod_cast total_pos P
  have hd : (0 : ℚ) < 10*(P.total : ℚ)^2 := by positivity
  rw [t,delta,one_div_mul_eq_div,div_le_iff₀ hd]
  nlinarith [sq_nonneg ((P.total : ℚ)-1)]

theorem c_pos (P : IntegerPartition) (i : Fin P.m) : 0 < P.c i := by
  have ht := t_pos P i
  have hb := t_le_tenth P i
  exact div_pos (by nlinarith : 0 < 1-P.t i^2) (by positivity)

theorem circle_identity (P : IntegerPartition) (i : Fin P.m) :
    P.c i^2+P.s i^2=1 := by
  have hd : 1+P.t i^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+P.t i^2)
  dsimp [c,s]
  field_simp [hd]
  <;> ring

theorem cos_theta (P : IntegerPartition) (i : Fin P.m) :
    Real.cos (P.theta i) = (P.c i : ℝ) := by
  rw [theta,Real.cos_two_mul,Real.cos_sq_arctan]
  push_cast [c]
  have hd : (1+(P.t i : ℝ)^2) ≠ 0 := ne_of_gt (by positivity)
  field_simp [hd]
  <;> ring

theorem sin_theta (P : IntegerPartition) (i : Fin P.m) :
    Real.sin (P.theta i) = (P.s i : ℝ) := by
  rw [theta,Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
  push_cast [s]
  have hs : Real.sqrt (1+(P.t i : ℝ)^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hsq := Real.sq_sqrt (show 0 ≤ 1+(P.t i : ℝ)^2 by positivity)
  have hd : 1+(P.t i : ℝ)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hs,hd]
  rw [hsq]

theorem rotation_companion_factorization (P : IntegerPartition) (i : Fin P.m) :
    companion (-(P.s i : ℝ)/(P.c i : ℝ)) (-1/(P.c i : ℝ)) *
      companion (P.s i : ℝ) (-(P.c i : ℝ)) = rotation (P.theta i) := by
  have hc : (P.c i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast c_pos P i)
  have hid : (P.c i : ℝ)^2+(P.s i : ℝ)^2=1 := by exact_mod_cast circle_identity P i
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [companion,rotation,Matrix.mul_apply,Fin.sum_univ_two,cos_theta,sin_theta] <;>
    field_simp [hc] <;> nlinarith [hid]

end IntegerPartition

theorem reflection_companion_factorization (q : ℝ) :
    companion 0 (-1)*companion 0 q = !![1,0;0,-q] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion,Matrix.mul_apply,Fin.sum_univ_two]

theorem rotation_mulVec (theta phi : ℝ) :
    (rotation theta).mulVec ![Real.cos phi,Real.sin phi] =
      ![Real.cos (theta+phi),Real.sin (theta+phi)] := by
  ext i
  fin_cases i <;> simp [rotation,Matrix.mulVec, dotProduct,Fin.sum_univ_two,
    Real.cos_add,Real.sin_add] <;> ring

end IV04.Paper
