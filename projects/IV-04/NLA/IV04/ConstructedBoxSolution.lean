module

public import NLA.IV04.PaperConstructedBox
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators Topology
namespace IV04.Paper

namespace IntegerPartition
theorem verified_layerCount_even (P : IntegerPartition) : Even P.layerCount := by
  exact layerCount_even P
end IntegerPartition


namespace IntegerPartition
theorem verified_layerCount_pos (P : IntegerPartition) : 0 < P.layerCount := by
  exact layerCount_pos P
end IntegerPartition


namespace IntegerPartition
theorem verified_extended_rotation_factorization (P : IntegerPartition) (k : ℕ) :
    companion (-(P.sAt k : ℝ)/(P.cAt k : ℝ)) (-1/(P.cAt k : ℝ))*
      companion (P.sAt k : ℝ) (-(P.cAt k : ℝ))=rotation (P.thetaAt k) := by
  exact extended_rotation_factorization P k
end IntegerPartition


namespace IntegerPartition
theorem verified_layer_rotation_factorization (P : IntegerPartition) (q : ℕ → ℝ) (k : ℕ) :
    companion (P.layerDiagonal (4*k+1) : ℝ) (P.layerBeta q (4*k+1))*
      companion (P.layerDiagonal (4*k) : ℝ) (P.layerBeta q (4*k))=
        rotation (P.thetaAt k) := by
  exact layer_rotation_factorization P q k
end IntegerPartition


namespace IntegerPartition
theorem verified_layer_reflection_factorization (P : IntegerPartition) (q : ℕ → ℝ) (k : ℕ) :
    companion (P.layerDiagonal (4*k+3) : ℝ) (P.layerBeta q (4*k+3))*
      companion (P.layerDiagonal (4*k+2) : ℝ) (P.layerBeta q (4*k+2))=
        reflection (q k) := by
  exact layer_reflection_factorization P q k
end IntegerPartition


namespace IntegerPartition
theorem verified_complete_layer_product (P : IntegerPartition) (q : ℕ → ℝ) (k : ℕ) :
    companionProduct (fun j => (P.layerDiagonal j : ℝ)) (P.layerBeta q) (4*k+2)=
      P.blockProduct q k := by
  exact complete_layer_product P q k
end IntegerPartition


namespace IntegerPartition
theorem verified_layer_determinant_block_transfer (P : IntegerPartition) (q : ℕ → ℝ) :
    (P.layerMatrix q).det =
      ((P.blockProduct q (P.m-1)).mulVec ![1,0]) 0 := by
  exact layer_determinant_block_transfer P q
end IntegerPartition


namespace IntegerPartition
theorem verified_reflection_mulVec (q phi : ℝ) (hq : q=-1 ∨ q=1) :
    (reflection q).mulVec ![Real.cos phi,Real.sin phi] =
      ![Real.cos (-q*phi),Real.sin (-q*phi)] := by
  exact reflection_mulVec q phi hq
end IntegerPartition


namespace IntegerPartition
theorem verified_block_vector_angles (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : ∀ k, q k=-1 ∨ q k=1) (k : ℕ) :
    (P.blockProduct q k).mulVec ![1,0]=
      ![Real.cos (P.endpointAngle (fun i => -q i) k),
        Real.sin (P.endpointAngle (fun i => -q i) k)] := by
  exact block_vector_angles P q hq k
end IntegerPartition


namespace IntegerPartition
theorem verified_endpoint_determinant_cosine (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : ∀ k, q k=-1 ∨ q k=1) :
    (P.layerMatrix q).det=
      Real.cos (P.endpointAngle (fun i => -q i) (P.m-1)) := by
  exact endpoint_determinant_cosine P q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_signAt_pattern (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (i : ℕ) :
    P.signAt sign i = -1 ∨ P.signAt sign i = 1 := by
  exact signAt_pattern P sign hs i
end IntegerPartition


namespace IntegerPartition
theorem verified_endpoint_parameters_vertices (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (i : ℕ) :
    P.endpointParameters sign i=-1 ∨ P.endpointParameters sign i=1 := by
  exact endpoint_parameters_vertices P sign hs i
end IntegerPartition


namespace IntegerPartition
theorem verified_endpoint_angle_signed_prefix (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (k : ℕ) :
    P.endpointAngle (fun i => -P.endpointParameters sign i) k=
      (P.signAt sign k : ℝ)*(∑ i ∈ Finset.range (k+1), (P.signAt sign i : ℝ)*P.thetaAt i) := by
  exact endpoint_angle_signed_prefix P sign hs k
end IntegerPartition


namespace IntegerPartition
theorem verified_full_signed_prefix (P : IntegerPartition) (sign : Fin P.m → ℤ) :
    (∑ i ∈ Finset.range P.m, (P.signAt sign i : ℝ)*P.thetaAt i)=P.signedAngle sign := by
  exact full_signed_prefix P sign
end IntegerPartition


namespace IntegerPartition
theorem verified_last_positive_layer_determinant (P : IntegerPartition) (sign : Fin P.m → ℤ)
    (hs : P.IsSignPattern sign) (hlast : sign P.lastIndex=1) :
    (P.layerMatrix (P.endpointParameters sign)).det=Real.cos (P.signedAngle sign) := by
  exact last_positive_layer_determinant P sign hs hlast
end IntegerPartition


namespace IntegerPartition
theorem verified_partition_layer_threshold_witness (P : IntegerPartition) (hp : P.HasPartition) :
    ∃ sign : Fin P.m → ℤ, P.IsSignPattern sign ∧ sign P.lastIndex=1 ∧
      (∀ i, P.endpointParameters sign i=-1 ∨ P.endpointParameters sign i=1) ∧
      (P.threshold : ℝ) ≤ (P.layerMatrix (P.endpointParameters sign)).det := by
  exact partition_layer_threshold_witness P hp
end IntegerPartition


namespace IntegerPartition
theorem verified_nonpartition_layer_endpoint_bound (P : IntegerPartition) (hp : ¬P.HasPartition)
    (sign : Fin P.m → ℤ) (hs : P.IsSignPattern sign) (hlast : sign P.lastIndex=1) :
    (P.layerMatrix (P.endpointParameters sign)).det ≤ 1-(361/300)*(P.delta : ℝ)^2 := by
  exact nonpartition_layer_endpoint_bound P hp sign hs hlast
end IntegerPartition


namespace IntegerPartition
theorem verified_layerMatrix_congr_parameters (P : IntegerPartition) (q r : ℕ → ℝ)
    (he : ∀ i < P.m-1, q i=r i) : P.layerMatrix q=P.layerMatrix r := by
  exact layerMatrix_congr_parameters P q r he
end IntegerPartition


namespace IntegerPartition
theorem verified_backward_sign_pattern (P : IntegerPartition) (q : ℕ → ℝ) (i : ℕ) :
    P.backwardSign q i=-1 ∨ P.backwardSign q i=1 := by
  exact backward_sign_pattern P q i
end IntegerPartition


namespace IntegerPartition
theorem verified_vertex_sign_pattern (P : IntegerPartition) (q : ℕ → ℝ) :
    P.IsSignPattern (P.vertexSign q) := by
  exact vertex_sign_pattern P q
end IntegerPartition


namespace IntegerPartition
theorem verified_vertex_sign_last (P : IntegerPartition) (q : ℕ → ℝ) :
    P.vertexSign q P.lastIndex=1 := by
  exact vertex_sign_last P q
end IntegerPartition


namespace IntegerPartition
theorem verified_backward_sign_step (P : IntegerPartition) (q : ℕ → ℝ) (i : ℕ)
    (hi : i < P.m-1) :
    P.backwardSign q i=(if q i=-1 then 1 else -1)*P.backwardSign q (i+1) := by
  exact backward_sign_step P q i hi
end IntegerPartition


namespace IntegerPartition
theorem verified_vertex_parameters_recover (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.IsVertex q) (i : ℕ) (hi : i < P.m-1) :
    P.endpointParameters (P.vertexSign q) i=q i := by
  exact vertex_parameters_recover P q hq i hi
end IntegerPartition


namespace IntegerPartition
theorem verified_every_vertex_determinant_cosine (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.IsVertex q) :
    (P.layerMatrix q).det=Real.cos (P.signedAngle (P.vertexSign q)) := by
  exact every_vertex_determinant_cosine P q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_every_vertex_positive (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.IsVertex q) : 0 < (P.layerMatrix q).det := by
  exact every_vertex_positive P q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_every_nonpartition_vertex_bound (P : IntegerPartition) (hp : ¬P.HasPartition)
    (q : ℕ → ℝ) (hq : P.IsVertex q) :
    (P.layerMatrix q).det ≤ 1-(361/300)*(P.delta : ℝ)^2 := by
  exact every_nonpartition_vertex_bound P hp q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_uncertain_entries_distinct (P : IntegerPartition) (k l : Fin (P.m-1))
    (he : P.uncertainRow k=P.uncertainRow l) : k=l := by
  exact uncertain_entries_distinct P k l he
end IntegerPartition


namespace IntegerPartition
theorem verified_uncertain_entry_value (P : IntegerPartition) (q : ℕ → ℝ) (k : Fin (P.m-1)) :
    P.layerMatrix q (P.uncertainRow k) (P.uncertainColumn k)=q k.val := by
  exact uncertain_entry_value P q k
end IntegerPartition


namespace IntegerPartition
theorem verified_layerMatrix_update_parameter (P : IntegerPartition) (q : ℕ → ℝ)
    (k : Fin (P.m-1)) (t : ℝ) :
    P.layerMatrix (Function.update q k.val t)=
      Matrix.updateRow (P.layerMatrix q) (P.uncertainRow k)
        (Function.update (P.layerMatrix q (P.uncertainRow k)) (P.uncertainColumn k) t) := by
  exact layerMatrix_update_parameter P q k t
end IntegerPartition


namespace IntegerPartition
theorem verified_determinant_parameter_interpolation (P : IntegerPartition) (q : ℕ → ℝ)
    (k : Fin (P.m-1)) (t : ℝ) :
    (P.layerMatrix (Function.update q k.val t)).det=
      ((1-t)/2)*(P.layerMatrix (Function.update q k.val (-1))).det+
        ((1+t)/2)*(P.layerMatrix (Function.update q k.val 1)).det := by
  exact determinant_parameter_interpolation P q k t
end IntegerPartition


namespace IntegerPartition
theorem verified_determinant_vertex_above (P : IntegerPartition) (q : ℕ → ℝ) (hq : P.InCube q) :
    ∃ r : ℕ → ℝ, P.IsVertex r ∧ (P.layerMatrix q).det ≤ (P.layerMatrix r).det := by
  exact determinant_vertex_above P q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_determinant_vertex_below (P : IntegerPartition) (q : ℕ → ℝ) (hq : P.InCube q) :
    ∃ r : ℕ → ℝ, P.IsVertex r ∧ (P.layerMatrix r).det ≤ (P.layerMatrix q).det := by
  exact determinant_vertex_below P q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_all_parameter_determinant_positive (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.InCube q) : 0 < (P.layerMatrix q).det := by
  exact all_parameter_determinant_positive P q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_all_nonpartition_determinant_bound (P : IntegerPartition) (hp : ¬P.HasPartition)
    (q : ℕ → ℝ) (hq : P.InCube q) :
    (P.layerMatrix q).det ≤ 1-(361/300)*(P.delta : ℝ)^2 := by
  exact all_nonpartition_determinant_bound P hp q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_partition_determinant_threshold (P : IntegerPartition) :
    P.HasPartition ↔ ∃ q : ℕ → ℝ, P.InCube q ∧
      (P.threshold : ℝ) ≤ (P.layerMatrix q).det := by
  exact partition_determinant_threshold P
end IntegerPartition


namespace IntegerPartition
theorem verified_fixed_entry_bounds (P : IntegerPartition) (q : ℕ → ℝ) (i j : Fin P.layerCount)
    (h : ¬(i.val=j.val+1 ∧ i.val%4=2)) :
    (P.rationalLower i j : ℝ)=P.layerMatrix q i j ∧
      (P.rationalUpper i j : ℝ)=P.layerMatrix q i j := by
  exact fixed_entry_bounds P q i j h
end IntegerPartition


namespace IntegerPartition
theorem verified_uncertain_entry_bounds (P : IntegerPartition) (k : Fin (P.m-1)) :
    P.rationalLower (P.uncertainRow k) (P.uncertainColumn k)=-1 ∧
      P.rationalUpper (P.uncertainRow k) (P.uncertainColumn k)=1 := by
  exact uncertain_entry_bounds P k
end IntegerPartition


namespace IntegerPartition
theorem verified_uncertain_position_indices (P : IntegerPartition) (i j : Fin P.layerCount)
    (h : i.val=j.val+1 ∧ i.val%4=2) :
    ∃ k : Fin (P.m-1), i=P.uncertainRow k ∧ j=P.uncertainColumn k := by
  exact uncertain_position_indices P i j h
end IntegerPartition


namespace IntegerPartition
theorem verified_layerMatrix_in_intervalBox (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.InCube q) : P.layerMatrix q ∈ P.intervalBox.realizations := by
  exact layerMatrix_in_intervalBox P q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_parametersOf_in_cube (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) : P.InCube (P.parametersOf A) := by
  exact parametersOf_in_cube P A hA
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_matrix_recovery (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) : A=P.layerMatrix (P.parametersOf A) := by
  exact intervalBox_matrix_recovery P A hA
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_realizations_exact (P : IntegerPartition) :
    P.intervalBox.realizations={A | ∃ q : ℕ → ℝ, P.InCube q ∧ A=P.layerMatrix q} := by
  exact intervalBox_realizations_exact P
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_regular (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) : 0 < A.det := by
  exact intervalBox_regular P A hA
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_partition_threshold (P : IntegerPartition) :
    P.HasPartition ↔ ∃ A ∈ P.intervalBox.realizations, (P.threshold : ℝ) ≤ A.det := by
  exact intervalBox_partition_threshold P
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_tridiagonal (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) : Tridiagonal A := by
  exact intervalBox_tridiagonal P A hA
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_nonempty (P : IntegerPartition) : P.intervalBox.realizations.Nonempty := by
  exact intervalBox_nonempty P
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_compact (P : IntegerPartition) : IsCompact P.intervalBox.realizations := by
  exact intervalBox_compact P
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_superdiagonal (P : IntegerPartition) (A : Mat P.layerCount)
    (hA : A ∈ P.intervalBox.realizations) (i j : Fin P.layerCount)
    (hj : j.val=i.val+1) : A i j=1 := by
  exact intervalBox_superdiagonal P A hA i j hj
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_attained_maximum (P : IntegerPartition) :
    ∃ A ∈ P.intervalBox.realizations,
      IsGreatest (Matrix.det '' P.intervalBox.realizations) A.det ∧
        (P.HasPartition ↔ (P.threshold : ℝ) ≤ A.det) := by
  exact intervalBox_attained_maximum P
end IntegerPartition


namespace IntegerPartition
theorem verified_intervalBox_vertex_maximum (P : IntegerPartition) :
    ∃ q : ℕ → ℝ, P.IsVertex q ∧ P.InCube q ∧
      IsGreatest (Matrix.det '' P.intervalBox.realizations) (P.layerMatrix q).det := by
  exact intervalBox_vertex_maximum P
end IntegerPartition


theorem verified_determinant_entry_interpolation (n : ℕ) (A : Mat n) (i j : Fin n) (t : ℝ) :
    (Matrix.updateRow A i (Function.update (A i) j t)).det=
      ((1-t)/2)*(Matrix.updateRow A i (Function.update (A i) j (-1))).det+
        ((1+t)/2)*(Matrix.updateRow A i (Function.update (A i) j 1)).det := by
  exact determinant_entry_interpolation n A i j t

theorem verified_affine_cube_vertex_above {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : (ι → ℝ) → ℝ)
    (haff : ∀ q i, i ∈ S → ∀ t : ℝ,
      f (Function.update q i t)=((1-t)/2)*f (Function.update q i (-1))+
        ((1+t)/2)*f (Function.update q i 1))
    (q : ι → ℝ) (hq : ∀ i ∈ S, -1 ≤ q i ∧ q i ≤ 1) :
    ∃ r : ι → ℝ, (∀ i ∈ S, r i=-1 ∨ r i=1) ∧
      (∀ i ∉ S, r i=q i) ∧ f q ≤ f r := by
  exact affine_cube_vertex_above S f haff q hq

theorem verified_affine_cube_vertex_below {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : (ι → ℝ) → ℝ)
    (haff : ∀ q i, i ∈ S → ∀ t : ℝ,
      f (Function.update q i t)=((1-t)/2)*f (Function.update q i (-1))+
        ((1+t)/2)*f (Function.update q i 1))
    (q : ι → ℝ) (hq : ∀ i ∈ S, -1 ≤ q i ∧ q i ≤ 1) :
    ∃ r : ι → ℝ, (∀ i ∈ S, r i=-1 ∨ r i=1) ∧
      (∀ i ∉ S, r i=q i) ∧ f r ≤ f q := by
  exact affine_cube_vertex_below S f haff q hq

#print axioms IV04.Paper.IntegerPartition.verified_layerCount_even
#print axioms IV04.Paper.IntegerPartition.verified_layerCount_pos
#print axioms IV04.Paper.IntegerPartition.verified_extended_rotation_factorization
#print axioms IV04.Paper.IntegerPartition.verified_layer_rotation_factorization
#print axioms IV04.Paper.IntegerPartition.verified_layer_reflection_factorization
#print axioms IV04.Paper.IntegerPartition.verified_complete_layer_product
#print axioms IV04.Paper.IntegerPartition.verified_layer_determinant_block_transfer
#print axioms IV04.Paper.IntegerPartition.verified_reflection_mulVec
#print axioms IV04.Paper.IntegerPartition.verified_block_vector_angles
#print axioms IV04.Paper.IntegerPartition.verified_endpoint_determinant_cosine
#print axioms IV04.Paper.IntegerPartition.verified_signAt_pattern
#print axioms IV04.Paper.IntegerPartition.verified_endpoint_parameters_vertices
#print axioms IV04.Paper.IntegerPartition.verified_endpoint_angle_signed_prefix
#print axioms IV04.Paper.IntegerPartition.verified_full_signed_prefix
#print axioms IV04.Paper.IntegerPartition.verified_last_positive_layer_determinant
#print axioms IV04.Paper.IntegerPartition.verified_partition_layer_threshold_witness
#print axioms IV04.Paper.IntegerPartition.verified_nonpartition_layer_endpoint_bound
#print axioms IV04.Paper.IntegerPartition.verified_layerMatrix_congr_parameters
#print axioms IV04.Paper.IntegerPartition.verified_backward_sign_pattern
#print axioms IV04.Paper.IntegerPartition.verified_vertex_sign_pattern
#print axioms IV04.Paper.IntegerPartition.verified_vertex_sign_last
#print axioms IV04.Paper.IntegerPartition.verified_backward_sign_step
#print axioms IV04.Paper.IntegerPartition.verified_vertex_parameters_recover
#print axioms IV04.Paper.IntegerPartition.verified_every_vertex_determinant_cosine
#print axioms IV04.Paper.IntegerPartition.verified_every_vertex_positive
#print axioms IV04.Paper.IntegerPartition.verified_every_nonpartition_vertex_bound
#print axioms IV04.Paper.IntegerPartition.verified_uncertain_entries_distinct
#print axioms IV04.Paper.IntegerPartition.verified_uncertain_entry_value
#print axioms IV04.Paper.IntegerPartition.verified_layerMatrix_update_parameter
#print axioms IV04.Paper.IntegerPartition.verified_determinant_parameter_interpolation
#print axioms IV04.Paper.IntegerPartition.verified_determinant_vertex_above
#print axioms IV04.Paper.IntegerPartition.verified_determinant_vertex_below
#print axioms IV04.Paper.IntegerPartition.verified_all_parameter_determinant_positive
#print axioms IV04.Paper.IntegerPartition.verified_all_nonpartition_determinant_bound
#print axioms IV04.Paper.IntegerPartition.verified_partition_determinant_threshold
#print axioms IV04.Paper.IntegerPartition.verified_fixed_entry_bounds
#print axioms IV04.Paper.IntegerPartition.verified_uncertain_entry_bounds
#print axioms IV04.Paper.IntegerPartition.verified_uncertain_position_indices
#print axioms IV04.Paper.IntegerPartition.verified_layerMatrix_in_intervalBox
#print axioms IV04.Paper.IntegerPartition.verified_parametersOf_in_cube
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_matrix_recovery
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_realizations_exact
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_regular
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_partition_threshold
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_tridiagonal
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_nonempty
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_compact
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_superdiagonal
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_attained_maximum
#print axioms IV04.Paper.IntegerPartition.verified_intervalBox_vertex_maximum
#print axioms IV04.Paper.verified_determinant_entry_interpolation
#print axioms IV04.Paper.verified_affine_cube_vertex_above
#print axioms IV04.Paper.verified_affine_cube_vertex_below
end IV04.Paper
