module

public import NLA.IV04.PaperLayerDefinitions
public import NLA.IV04.PaperPartitionRotations
public import NLA.IV04.PaperContinuantIdentity

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

theorem layerCount_even (P : IntegerPartition) : Even P.layerCount := by
  refine ⟨2*(P.m-1)+1,?_⟩
  have := P.nonempty
  dsimp [layerCount]
  omega

theorem layerCount_pos (P : IntegerPartition) : 0 < P.layerCount := by
  have := P.nonempty
  dsimp [layerCount]
  omega

theorem extended_rotation_factorization (P : IntegerPartition) (k : ℕ) :
    companion (-(P.sAt k : ℝ)/(P.cAt k : ℝ)) (-1/(P.cAt k : ℝ))*
      companion (P.sAt k : ℝ) (-(P.cAt k : ℝ))=rotation (P.thetaAt k) := by
  by_cases h : k < P.m
  · simpa only [sAt,cAt,thetaAt,dif_pos h] using rotation_companion_factorization P ⟨k,h⟩
  · simp [sAt,cAt,thetaAt,h,rotation,companion,Matrix.mul_apply,Fin.sum_univ_two]

theorem layer_rotation_factorization (P : IntegerPartition) (q : ℕ → ℝ) (k : ℕ) :
    companion (P.layerDiagonal (4*k+1) : ℝ) (P.layerBeta q (4*k+1))*
      companion (P.layerDiagonal (4*k) : ℝ) (P.layerBeta q (4*k))=
        rotation (P.thetaAt k) := by
  have h0 : (4*k)%4=0 := by omega
  have h1 : (4*k+1)%4=1 := by omega
  have d0 : (4*k)/4=k := by omega
  have d1 : (4*k+1)/4=k := by omega
  simpa [layerDiagonal,layerBeta,h0,h1,d0,d1] using extended_rotation_factorization P k

theorem layer_reflection_factorization (P : IntegerPartition) (q : ℕ → ℝ) (k : ℕ) :
    companion (P.layerDiagonal (4*k+3) : ℝ) (P.layerBeta q (4*k+3))*
      companion (P.layerDiagonal (4*k+2) : ℝ) (P.layerBeta q (4*k+2))=
        reflection (q k) := by
  have h2 : (4*k+2)%4=2 := by omega
  have h3 : (4*k+3)%4=3 := by omega
  have d2 : (4*k+2)/4=k := by omega
  simpa [layerDiagonal,layerBeta,h2,h3,d2,reflection] using reflection_companion_factorization (q k)

theorem complete_layer_product (P : IntegerPartition) (q : ℕ → ℝ) (k : ℕ) :
    companionProduct (fun j => (P.layerDiagonal j : ℝ)) (P.layerBeta q) (4*k+2)=
      P.blockProduct q k := by
  induction k with
  | zero =>
    simpa [companionProduct,blockProduct] using layer_rotation_factorization P q 0
  | succ k ih =>
    have hidx : 4*(k+1)+2=(4*k+2)+1+1+1+1 := by omega
    rw [hidx,companionProduct,companionProduct,companionProduct,companionProduct,ih]
    have h4 : 4*k+2+1+1=4*(k+1) := by omega
    have h5 : 4*k+2+1+1+1=4*(k+1)+1 := by omega
    have h3 : 4*k+2+1=4*k+3 := by omega
    rw [h4,h5,h3]
    change _ = rotation (P.thetaAt (k+1))*reflection (q k)*P.blockProduct q k
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc]
    rw [layer_rotation_factorization]
    rw [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (rotation (P.thetaAt (k+1)))]
    rw [layer_reflection_factorization]

theorem layer_determinant_block_transfer (P : IntegerPartition) (q : ℕ → ℝ) :
    (P.layerMatrix q).det =
      ((P.blockProduct q (P.m-1)).mulVec ![1,0]) 0 := by
  have hn : P.layerCount=4*(P.m-1)+2 := by
    have := P.nonempty
    dsimp [layerCount]
    omega
  rw [layerMatrix,continuant_determinant_transfer,hn,complete_layer_product]

theorem reflection_mulVec (q phi : ℝ) (hq : q=-1 ∨ q=1) :
    (reflection q).mulVec ![Real.cos phi,Real.sin phi] =
      ![Real.cos (-q*phi),Real.sin (-q*phi)] := by
  rcases hq with rfl | rfl <;>
    ext i <;> fin_cases i <;>
    simp [reflection,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Real.cos_neg,Real.sin_neg]

theorem block_vector_angles (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : ∀ k, q k=-1 ∨ q k=1) (k : ℕ) :
    (P.blockProduct q k).mulVec ![1,0]=
      ![Real.cos (P.endpointAngle (fun i => -q i) k),
        Real.sin (P.endpointAngle (fun i => -q i) k)] := by
  induction k with
  | zero =>
    ext i
    fin_cases i
    all_goals
      simp [blockProduct,endpointAngle,rotation,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  | succ k ih =>
    rw [blockProduct,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,ih,
      reflection_mulVec _ _ (hq k),rotation_mulVec]
    rfl

theorem endpoint_determinant_cosine (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : ∀ k, q k=-1 ∨ q k=1) :
    (P.layerMatrix q).det=
      Real.cos (P.endpointAngle (fun i => -q i) (P.m-1)) := by
  rw [layer_determinant_block_transfer,block_vector_angles P q hq]
  rfl

end IV04.Paper.IntegerPartition
