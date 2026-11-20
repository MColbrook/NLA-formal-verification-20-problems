module

public import NLA.IV04.PaperPartitionBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace IV04.Paper.IntegerPartition

theorem signed_angle_error (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) :
    |P.signedAngle sign-2*(P.delta : ℝ)*(P.signedWeight sign : ℝ)| ≤ P.error := by
  have he : P.signedAngle sign-2*(P.delta : ℝ)*(P.signedWeight sign : ℝ)=
      ∑ i, (sign i : ℝ)*(P.theta i-2*(P.delta : ℝ)*P.weight i) := by
    simp only [signedAngle,signedWeight,Int.cast_sum,Int.cast_mul,Int.cast_natCast,
      Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    |∑ i, (sign i : ℝ)*(P.theta i-2*(P.delta : ℝ)*P.weight i)| ≤
        ∑ i, |(sign i : ℝ)*(P.theta i-2*(P.delta : ℝ)*P.weight i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = P.error := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hs i with h | h <;> simp [h,abs_mul,abs_sub_comm]

theorem signed_angle_small (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) : |P.signedAngle sign| ≤ 1/5 := by
  calc
    |P.signedAngle sign| ≤ ∑ i, |(sign i : ℝ)*P.theta i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, P.theta i := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hs i with h | h <;> simp [h,abs_of_nonneg (theta_nonneg P i)]
    _ ≤ 1/5 := total_angle_le P

theorem signed_angle_positive_cosine (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) : 0 < Real.cos (P.signedAngle sign) := by
  exact Real.cos_pos_of_le_one (by linarith [signed_angle_small P sign hs])

theorem partition_angle_bound (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hw : P.signedWeight sign=0) :
    |P.signedAngle sign| ≤ (P.delta : ℝ)/10 := by
  have hb := (signed_angle_error P sign hs).trans (error_le_delta_tenth P)
  simpa [hw] using hb

theorem nonpartition_angle_bound (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hw : P.signedWeight sign ≠ 0) :
    19*(P.delta : ℝ)/10 ≤ |P.signedAngle sign| := by
  have hint : (1 : ℤ) ≤ |P.signedWeight sign| := by
    by_contra h
    have ha := abs_lt.mp (lt_of_not_ge h)
    omega
  have hr : (1 : ℝ) ≤ |(P.signedWeight sign : ℝ)| := by exact_mod_cast hint
  have hdelta : (0 : ℝ) < P.delta := by exact_mod_cast delta_pos P
  have hb := (signed_angle_error P sign hs).trans (error_le_delta_tenth P)
  have htri := abs_add_le (P.signedAngle sign)
    (2*(P.delta : ℝ)*(P.signedWeight sign : ℝ)-P.signedAngle sign)
  have habs : |2*(P.delta : ℝ)*(P.signedWeight sign : ℝ)| =
      2*(P.delta : ℝ)*|(P.signedWeight sign : ℝ)| := by
    rw [abs_mul,abs_of_nonneg (by positivity)]
  rw [add_sub_cancel,habs,abs_sub_comm] at htri
  nlinarith

theorem partition_cosine_bound (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hw : P.signedWeight sign=0) :
    1-(P.delta : ℝ)^2/200 ≤ Real.cos (P.signedAngle sign) := by
  have hb := partition_angle_bound P sign hs hw
  have hd : (0 : ℝ) < P.delta := by exact_mod_cast delta_pos P
  have hsq : (P.signedAngle sign)^2 ≤ (P.delta : ℝ)^2/100 := by
    nlinarith [sq_abs (P.signedAngle sign),abs_nonneg (P.signedAngle sign),
      mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ (P.delta : ℝ)/10+|P.signedAngle sign| by positivity)]
  linarith [Real.one_sub_sq_div_two_le_cos (x := P.signedAngle sign)]

theorem nonpartition_cosine_bound (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hw : P.signedWeight sign ≠ 0) :
    Real.cos (P.signedAngle sign) ≤ 1-(361/300)*(P.delta : ℝ)^2 := by
  have hb := nonpartition_angle_bound P sign hs hw
  have hd : (0 : ℝ) < P.delta := by exact_mod_cast delta_pos P
  have hsq : (361/100)*(P.delta : ℝ)^2 ≤ (P.signedAngle sign)^2 := by
    nlinarith [sq_abs (P.signedAngle sign),abs_nonneg (P.signedAngle sign),
      mul_nonneg (sub_nonneg.mpr hb)
        (show 0 ≤ |P.signedAngle sign|+19*(P.delta : ℝ)/10 by positivity)]
  have hc := cosine_quadratic_upper (P.signedAngle sign)
    (by linarith [signed_angle_small P sign hs])
  linarith

theorem partition_threshold_separation (P : IntegerPartition) :
    P.HasPartition ↔ ∃ sign : Fin P.m → ℤ,
      P.IsSignPattern sign ∧ (P.threshold : ℝ) ≤ Real.cos (P.signedAngle sign) := by
  have hd : (0 : ℝ) < P.delta := by exact_mod_cast delta_pos P
  have ht : (P.threshold : ℝ)=1-(P.delta : ℝ)^2/2 := by simp [threshold]
  constructor
  · rintro ⟨sign,hs,hw⟩
    refine ⟨sign,hs,?_⟩
    rw [ht]
    linarith [partition_cosine_bound P sign hs hw,sq_pos_of_pos hd]
  · rintro ⟨sign,hs,hc⟩
    refine ⟨sign,hs,?_⟩
    by_contra hw
    have hb := nonpartition_cosine_bound P sign hs hw
    rw [ht] at hc
    nlinarith [sq_pos_of_pos hd]

theorem reverse_signed_weight (P : IntegerPartition) (sign : Fin P.m → ℤ) :
    P.signedWeight (fun i => -sign i) = -P.signedWeight sign := by
  simp [signedWeight,Finset.sum_neg_distrib]

theorem partition_last_positive (P : IntegerPartition) :
    P.HasPartition ↔ ∃ sign : Fin P.m → ℤ,
      P.IsSignPattern sign ∧ P.signedWeight sign=0 ∧
        sign P.lastIndex=1 := by
  constructor
  · rintro ⟨sign,hs,hw⟩
    let last : Fin P.m := ⟨P.m-1,by have := P.nonempty; omega⟩
    rcases hs last with hn | hp
    · refine ⟨fun i => -sign i,?_,?_,?_⟩
      · intro i
        rcases hs i with h | h <;> simp [h]
      · simp [reverse_signed_weight,hw]
      · simpa [lastIndex,last] using congrArg Neg.neg hn
    · exact ⟨sign,hs,hw,hp⟩
  · rintro ⟨sign,hs,hw,_⟩
    exact ⟨sign,hs,hw⟩

end IV04.Paper.IntegerPartition
