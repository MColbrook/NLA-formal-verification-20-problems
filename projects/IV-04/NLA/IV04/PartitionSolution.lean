module

public import NLA.IV04.PaperPartitionSeparation
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper

namespace IntegerPartition
theorem verified_weight_le_total (P : IntegerPartition) (i : Fin P.m) :
    P.weight i ≤ P.total := by
  exact weight_le_total P i
end IntegerPartition


namespace IntegerPartition
theorem verified_total_pos (P : IntegerPartition) : 0 < P.total := by
  exact total_pos P
end IntegerPartition


namespace IntegerPartition
theorem verified_delta_pos (P : IntegerPartition) : 0 < P.delta := by
  exact delta_pos P
end IntegerPartition


namespace IntegerPartition
theorem verified_delta_le_tenth (P : IntegerPartition) : P.delta ≤ 1/10 := by
  exact delta_le_tenth P
end IntegerPartition


namespace IntegerPartition
theorem verified_t_pos (P : IntegerPartition) (i : Fin P.m) : 0 < P.t i := by
  exact t_pos P i
end IntegerPartition


namespace IntegerPartition
theorem verified_t_le_tenth (P : IntegerPartition) (i : Fin P.m) : P.t i ≤ 1/10 := by
  exact t_le_tenth P i
end IntegerPartition


namespace IntegerPartition
theorem verified_c_pos (P : IntegerPartition) (i : Fin P.m) : 0 < P.c i := by
  exact c_pos P i
end IntegerPartition


namespace IntegerPartition
theorem verified_circle_identity (P : IntegerPartition) (i : Fin P.m) :
    P.c i^2+P.s i^2=1 := by
  exact circle_identity P i
end IntegerPartition


namespace IntegerPartition
theorem verified_cos_theta (P : IntegerPartition) (i : Fin P.m) :
    Real.cos (P.theta i) = (P.c i : ℝ) := by
  exact cos_theta P i
end IntegerPartition


namespace IntegerPartition
theorem verified_sin_theta (P : IntegerPartition) (i : Fin P.m) :
    Real.sin (P.theta i) = (P.s i : ℝ) := by
  exact sin_theta P i
end IntegerPartition


namespace IntegerPartition
theorem verified_rotation_companion_factorization (P : IntegerPartition) (i : Fin P.m) :
    companion (-(P.s i : ℝ)/(P.c i : ℝ)) (-1/(P.c i : ℝ)) *
      companion (P.s i : ℝ) (-(P.c i : ℝ)) = rotation (P.theta i) := by
  exact rotation_companion_factorization P i
end IntegerPartition


theorem verified_reflection_companion_factorization (q : ℝ) :
    companion 0 (-1)*companion 0 q = !![1,0;0,-q] := by
  exact reflection_companion_factorization q

theorem verified_rotation_mulVec (theta phi : ℝ) :
    (rotation theta).mulVec ![Real.cos phi,Real.sin phi] =
      ![Real.cos (theta+phi),Real.sin (theta+phi)] := by
  exact rotation_mulVec theta phi

theorem verified_arctan_cubic_error (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ 2*t-2*Real.arctan t ∧ 2*t-2*Real.arctan t ≤ (2/3)*t^3 := by
  exact arctan_cubic_error t ht

theorem verified_cosine_quadratic_upper (x : ℝ) (hx : |x| ≤ 1) :
    Real.cos x ≤ 1-x^2/3 := by
  exact cosine_quadratic_upper x hx

theorem verified_sum_cubes_le_cube_sum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∑ i ∈ S, f i^3) ≤ (∑ i ∈ S, f i)^3 := by
  exact sum_cubes_le_cube_sum S f hf

namespace IntegerPartition
theorem verified_sum_t (P : IntegerPartition) :
    (∑ i, (P.t i : ℝ)) = (P.delta : ℝ)*P.total := by
  exact sum_t P
end IntegerPartition


namespace IntegerPartition
theorem verified_theta_nonneg (P : IntegerPartition) (i : Fin P.m) : 0 ≤ P.theta i := by
  exact theta_nonneg P i
end IntegerPartition


namespace IntegerPartition
theorem verified_theta_le_scaled_weight (P : IntegerPartition) (i : Fin P.m) :
    P.theta i ≤ 2*(P.delta : ℝ)*P.weight i := by
  exact theta_le_scaled_weight P i
end IntegerPartition


namespace IntegerPartition
theorem verified_total_angle_le (P : IntegerPartition) : (∑ i, P.theta i) ≤ 1/5 := by
  exact total_angle_le P
end IntegerPartition


namespace IntegerPartition
theorem verified_error_le_cubic (P : IntegerPartition) :
    P.error ≤ (2/3)*((P.delta : ℝ)*P.total)^3 := by
  exact error_le_cubic P
end IntegerPartition


namespace IntegerPartition
theorem verified_cubic_error_identity (P : IntegerPartition) :
    (2/3)*((P.delta : ℝ)*P.total)^3 = (P.delta : ℝ)/(150*P.total) := by
  exact cubic_error_identity P
end IntegerPartition


namespace IntegerPartition
theorem verified_error_le_delta_tenth (P : IntegerPartition) : P.error ≤ (P.delta : ℝ)/10 := by
  exact error_le_delta_tenth P
end IntegerPartition


namespace IntegerPartition
theorem verified_signed_angle_error (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) :
    |P.signedAngle sign-2*(P.delta : ℝ)*(P.signedWeight sign : ℝ)| ≤ P.error := by
  exact signed_angle_error P sign hs
end IntegerPartition


namespace IntegerPartition
theorem verified_signed_angle_small (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) : |P.signedAngle sign| ≤ 1/5 := by
  exact signed_angle_small P sign hs
end IntegerPartition


namespace IntegerPartition
theorem verified_signed_angle_positive_cosine (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) : 0 < Real.cos (P.signedAngle sign) := by
  exact signed_angle_positive_cosine P sign hs
end IntegerPartition


namespace IntegerPartition
theorem verified_partition_angle_bound (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hw : P.signedWeight sign=0) :
    |P.signedAngle sign| ≤ (P.delta : ℝ)/10 := by
  exact partition_angle_bound P sign hs hw
end IntegerPartition


namespace IntegerPartition
theorem verified_nonpartition_angle_bound (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hw : P.signedWeight sign ≠ 0) :
    19*(P.delta : ℝ)/10 ≤ |P.signedAngle sign| := by
  exact nonpartition_angle_bound P sign hs hw
end IntegerPartition


namespace IntegerPartition
theorem verified_partition_cosine_bound (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hw : P.signedWeight sign=0) :
    1-(P.delta : ℝ)^2/200 ≤ Real.cos (P.signedAngle sign) := by
  exact partition_cosine_bound P sign hs hw
end IntegerPartition


namespace IntegerPartition
theorem verified_nonpartition_cosine_bound (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hw : P.signedWeight sign ≠ 0) :
    Real.cos (P.signedAngle sign) ≤ 1-(361/300)*(P.delta : ℝ)^2 := by
  exact nonpartition_cosine_bound P sign hs hw
end IntegerPartition


namespace IntegerPartition
theorem verified_partition_threshold_separation (P : IntegerPartition) :
    P.HasPartition ↔ ∃ sign : Fin P.m → ℤ,
      P.IsSignPattern sign ∧ (P.threshold : ℝ) ≤ Real.cos (P.signedAngle sign) := by
  exact partition_threshold_separation P
end IntegerPartition


namespace IntegerPartition
theorem verified_reverse_signed_weight (P : IntegerPartition) (sign : Fin P.m → ℤ) :
    P.signedWeight (fun i => -sign i) = -P.signedWeight sign := by
  exact reverse_signed_weight P sign
end IntegerPartition


namespace IntegerPartition
theorem verified_partition_last_positive (P : IntegerPartition) :
    P.HasPartition ↔ ∃ sign : Fin P.m → ℤ,
      P.IsSignPattern sign ∧ P.signedWeight sign=0 ∧
        sign P.lastIndex=1 := by
  exact partition_last_positive P
end IntegerPartition


#print axioms IV04.Paper.IntegerPartition.verified_weight_le_total
#print axioms IV04.Paper.IntegerPartition.verified_total_pos
#print axioms IV04.Paper.IntegerPartition.verified_delta_pos
#print axioms IV04.Paper.IntegerPartition.verified_delta_le_tenth
#print axioms IV04.Paper.IntegerPartition.verified_t_pos
#print axioms IV04.Paper.IntegerPartition.verified_t_le_tenth
#print axioms IV04.Paper.IntegerPartition.verified_c_pos
#print axioms IV04.Paper.IntegerPartition.verified_circle_identity
#print axioms IV04.Paper.IntegerPartition.verified_cos_theta
#print axioms IV04.Paper.IntegerPartition.verified_sin_theta
#print axioms IV04.Paper.IntegerPartition.verified_rotation_companion_factorization
#print axioms IV04.Paper.verified_reflection_companion_factorization
#print axioms IV04.Paper.verified_rotation_mulVec
#print axioms IV04.Paper.verified_arctan_cubic_error
#print axioms IV04.Paper.verified_cosine_quadratic_upper
#print axioms IV04.Paper.verified_sum_cubes_le_cube_sum
#print axioms IV04.Paper.IntegerPartition.verified_sum_t
#print axioms IV04.Paper.IntegerPartition.verified_theta_nonneg
#print axioms IV04.Paper.IntegerPartition.verified_theta_le_scaled_weight
#print axioms IV04.Paper.IntegerPartition.verified_total_angle_le
#print axioms IV04.Paper.IntegerPartition.verified_error_le_cubic
#print axioms IV04.Paper.IntegerPartition.verified_cubic_error_identity
#print axioms IV04.Paper.IntegerPartition.verified_error_le_delta_tenth
#print axioms IV04.Paper.IntegerPartition.verified_signed_angle_error
#print axioms IV04.Paper.IntegerPartition.verified_signed_angle_small
#print axioms IV04.Paper.IntegerPartition.verified_signed_angle_positive_cosine
#print axioms IV04.Paper.IntegerPartition.verified_partition_angle_bound
#print axioms IV04.Paper.IntegerPartition.verified_nonpartition_angle_bound
#print axioms IV04.Paper.IntegerPartition.verified_partition_cosine_bound
#print axioms IV04.Paper.IntegerPartition.verified_nonpartition_cosine_bound
#print axioms IV04.Paper.IntegerPartition.verified_partition_threshold_separation
#print axioms IV04.Paper.IntegerPartition.verified_reverse_signed_weight
#print axioms IV04.Paper.IntegerPartition.verified_partition_last_positive
end IV04.Paper
