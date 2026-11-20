module

public import NLA.RA08.LiteralContour.NuclearDefinitions
public import NLA.RA08.PaperNuclearTriangularError
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical Matrix BigOperators

namespace NLA.RA08.Paper.LiteralContour

theorem upper_distance_exact (m : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0) :
    (∑ i : Fin m, ∑ j : Fin m, if i < j then f (j.val-i.val) else 0) =
      ∑ d ∈ Finset.range m, (m-d : ℕ)*f d := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrec : (∑ i : Fin (m+1), ∑ j : Fin (m+1),
        if i < j then f (j.val-i.val) else 0) =
        (∑ j : Fin m, f (j.val+1))+
        ∑ i : Fin m, ∑ j : Fin m, if i < j then f (j.val-i.val) else 0 := by
      rw [Fin.sum_univ_succ]
      have hpos (j : Fin m) : (0 : Fin (m+1)) < j.succ := Nat.zero_lt_succ _
      simp only [Fin.sum_univ_succ,hpos,Fin.not_lt_zero,Fin.succ_lt_succ_iff,
        if_true,if_false,Fin.val_zero,Fin.val_succ,Nat.sub_zero,Nat.add_sub_add_right,
        zero_add]
    have hfin : (∑ j : Fin m, f (j.val+1)) = ∑ j ∈ Finset.range m, f (j+1) :=
      Fin.sum_univ_eq_sum_range (fun j => f (j+1)) m
    rw [hrec,ih,hfin]
    rw [Finset.sum_range_succ]
    have hsum : (∑ d ∈ Finset.range m, (m+1-d : ℕ)*f d) =
        (∑ d ∈ Finset.range m, (m-d : ℕ)*f d)+(∑ d ∈ Finset.range m, f d) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hd' := Finset.mem_range.mp hd
      have he : m+1-d=(m-d)+1 := by omega
      rw [he,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    rw [hsum]
    have hshift := Finset.sum_range_succ' f m
    rw [Finset.sum_range_succ,h0,add_zero] at hshift
    norm_num only [Nat.add_sub_cancel_left,Nat.cast_one,one_mul]
    linarith

theorem nuclear_error_entry_exact {m : ℕ} (i j : Fin m) :
    ((nuclearKernel m-(nuclearTriangular m-(1/2 : ℝ) • (1 : RealMatrix m))) i j)^2 =
      (if i < j then distanceError (j.val-i.val) else 0)+
      (if j < i then distanceError (i.val-j.val) else 0) := by
  rcases lt_trichotomy i j with hij|hij|hji
  · have hne : i ≠ j := ne_of_lt hij
    have hd : j.val-i.val ≠ 0 := by omega
    simp only [Matrix.sub_apply,nuclearTriangular,if_pos hij.le,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply_ne hne,mul_zero,sub_zero,if_pos hij,
      if_neg (not_lt_of_ge hij.le),add_zero,distanceError,if_neg hd,
      nuclearKernel_above_formula i j hij.le]
    have hp : 1+(1/4 : ℝ)^(j.val-i.val) ≠ 0 := by positivity
    field_simp
    ring
  · subst j
    norm_num [nuclearKernel_diagonal,nuclearTriangular]
  · have hne : i ≠ j := Ne.symm (ne_of_lt hji)
    have hd : i.val-j.val ≠ 0 := by omega
    have hk : nuclearKernel m i j = 1-1/(1+(1/4 : ℝ)^(i.val-j.val)) := by
      have h := nuclearKernel_complement i j
      rw [nuclearKernel_above_formula j i hji.le] at h
      linarith
    simp only [Matrix.sub_apply,nuclearTriangular,if_neg (not_le_of_gt hji),Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply_ne hne,mul_zero,sub_zero,if_pos hji,
      if_neg (not_lt_of_ge hji.le),zero_add,distanceError,if_neg hd,hk]
    have hp : 1+(1/4 : ℝ)^(i.val-j.val) ≠ 0 := by positivity
    field_simp
    ring

theorem actual_nuclear_distance_sum (m : ℕ) :
    frobeniusSquared (nuclearKernel m-(nuclearTriangular m-(1/2 : ℝ) • (1 : RealMatrix m))) =
      2*∑ d ∈ Finset.Ico 1 m, (m-d : ℕ)*
        ((1/4 : ℝ)^d/(1+(1/4 : ℝ)^d))^2 := by
  unfold frobeniusSquared
  simp_rw [nuclear_error_entry_exact,Finset.sum_add_distrib]
  have hsym : (∑ i : Fin m, ∑ j : Fin m,
      if j < i then distanceError (i.val-j.val) else 0) =
      ∑ i : Fin m, ∑ j : Fin m, if i < j then distanceError (j.val-i.val) else 0 :=
    Finset.sum_comm
  rw [hsym,upper_distance_exact m distanceError (by simp [distanceError])]
  have hr : (∑ d ∈ Finset.range m, (m-d : ℕ)*distanceError d) =
      ∑ d ∈ Finset.Ico 1 m, (m-d : ℕ)*((1/4 : ℝ)^d/(1+(1/4 : ℝ)^d))^2 := by
    by_cases hm : m=0
    · subst m; simp
    · have h := Finset.sum_Ico_consecutive (fun d => (m-d : ℕ)*distanceError d)
        (by omega : 0 ≤ 1) (by omega : 1 ≤ m)
      have hz : distanceError 0 = 0 := by simp [distanceError]
      simp only [Nat.Ico_zero_eq_range,Finset.sum_range_one,hz,mul_zero,zero_add] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := by have := (Finset.mem_Ico.mp hd).1; omega
      simp only [distanceError,if_neg hd0]
  rw [hr]
  ring

theorem actual_nuclear_distance_bound (m : ℕ) :
    frobeniusSquared (nuclearKernel m-(nuclearTriangular m-(1/2 : ℝ) • (1 : RealMatrix m))) ≤
      2*m*(1/4 : ℝ)^2/(1-(1/4 : ℝ)^2) := by
  convert nuclearTriangular_error_frobenius_squared m using 1 <;> ring

#print axioms actual_nuclear_distance_sum

end NLA.RA08.Paper.LiteralContour
