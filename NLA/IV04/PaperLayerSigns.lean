module

public import NLA.IV04.PaperLayerSignDefinitions
public import NLA.IV04.PaperLayerTransfer
public import NLA.IV04.PaperPartitionSeparation

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

theorem signAt_pattern (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (i : ℕ) :
    P.signAt sign i = -1 ∨ P.signAt sign i = 1 := by
  by_cases hi : i < P.m
  · simpa only [signAt,dif_pos hi] using hs ⟨i,hi⟩
  · simp [signAt,hi]

theorem endpoint_parameters_vertices (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (i : ℕ) :
    P.endpointParameters sign i=-1 ∨ P.endpointParameters sign i=1 := by
  rcases signAt_pattern P sign hs i with ha | ha <;>
    rcases signAt_pattern P sign hs (i+1) with hb | hb <;>
    simp [endpointParameters,ha,hb]

theorem endpoint_angle_signed_prefix (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (k : ℕ) :
    P.endpointAngle (fun i => -P.endpointParameters sign i) k=
      (P.signAt sign k : ℝ)*(∑ i ∈ Finset.range (k+1), (P.signAt sign i : ℝ)*P.thetaAt i) := by
  induction k with
  | zero =>
    rcases signAt_pattern P sign hs 0 with h | h <;>
      simp [endpointAngle,Finset.sum_range_one,h]
  | succ k ih =>
    rw [endpointAngle,ih,Finset.sum_range_succ _ (k+1)]
    rcases signAt_pattern P sign hs k with ha | ha <;>
      rcases signAt_pattern P sign hs (k+1) with hb | hb <;>
      simp [endpointParameters,ha,hb] <;> ring

theorem full_signed_prefix (P : IntegerPartition) (sign : Fin P.m → ℤ) :
    (∑ i ∈ Finset.range P.m, (P.signAt sign i : ℝ)*P.thetaAt i)=P.signedAngle sign := by
  rw [signedAngle]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [signAt,thetaAt,i.isLt]

theorem last_positive_layer_determinant (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hlast : sign P.lastIndex=1) :
    (P.layerMatrix (P.endpointParameters sign)).det=Real.cos (P.signedAngle sign) := by
  rw [endpoint_determinant_cosine P _ (endpoint_parameters_vertices P sign hs),
    endpoint_angle_signed_prefix P sign hs]
  have hi : P.m-1 < P.m := Nat.sub_lt P.nonempty (by decide)
  have hm : P.m-1+1=P.m := by have := P.nonempty; omega
  have hlast' : P.signAt sign (P.m-1)=1 := by simpa [signAt,hi,lastIndex] using hlast
  rw [hm,full_signed_prefix,hlast']
  simp

theorem partition_layer_threshold_witness (P : IntegerPartition) (hp : P.HasPartition) :
    ∃ sign : Fin P.m → ℤ, P.IsSignPattern sign ∧ sign P.lastIndex=1 ∧
      (∀ i, P.endpointParameters sign i=-1 ∨ P.endpointParameters sign i=1) ∧
      (P.threshold : ℝ) ≤ (P.layerMatrix (P.endpointParameters sign)).det := by
  obtain ⟨sign,hs,hw,hlast⟩ := (partition_last_positive P).mp hp
  refine ⟨sign,hs,hlast,endpoint_parameters_vertices P sign hs,?_⟩
  rw [last_positive_layer_determinant P sign hs hlast]
  have hd : (0 : ℝ) < P.delta := by exact_mod_cast delta_pos P
  simp only [threshold,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  linarith [partition_cosine_bound P sign hs hw,sq_pos_of_pos hd]

theorem nonpartition_layer_endpoint_bound (P : IntegerPartition) (hp : ¬P.HasPartition)
    (sign : Fin P.m → ℤ) (hs : P.IsSignPattern sign) (hlast : sign P.lastIndex=1) :
    (P.layerMatrix (P.endpointParameters sign)).det ≤ 1-(361/300)*(P.delta : ℝ)^2 := by
  rw [last_positive_layer_determinant P sign hs hlast]
  exact nonpartition_cosine_bound P sign hs (fun hw => hp ⟨sign,hs,hw⟩)

end IV04.Paper.IntegerPartition
