module

public import NLA.IV04.PaperVertexDefinitions
public import NLA.IV04.PaperLayerSigns

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

theorem layerMatrix_congr_parameters (P : IntegerPartition) (q r : ℕ → ℝ)
    (he : ∀ i < P.m-1, q i=r i) : P.layerMatrix q=P.layerMatrix r := by
  ext i j
  dsimp [layerMatrix,continuantMatrix]
  split_ifs with hd hu hl
  · rfl
  · rfl
  · dsimp [layerBeta]
    split_ifs with h0 h1 h2
    · rfl
    · rfl
    · apply he
      have hi := i.isLt
      dsimp [layerCount] at hi
      omega
    · rfl
  · rfl

theorem backward_sign_pattern (P : IntegerPartition) (q : ℕ → ℝ) (i : ℕ) :
    P.backwardSign q i=-1 ∨ P.backwardSign q i=1 := by
  have h : ∀ S : Finset ℕ,
      (∏ j ∈ S, if q j=-1 then (1 : ℤ) else -1)=-1 ∨
      (∏ j ∈ S, if q j=-1 then (1 : ℤ) else -1)=1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      rw [Finset.prod_insert ha]
      by_cases hq : q a=-1 <;> rcases ih with h | h <;> simp [hq,h]
  exact h _

theorem vertex_sign_pattern (P : IntegerPartition) (q : ℕ → ℝ) :
    P.IsSignPattern (P.vertexSign q) := by
  intro i
  exact backward_sign_pattern P q i.val

theorem vertex_sign_last (P : IntegerPartition) (q : ℕ → ℝ) :
    P.vertexSign q P.lastIndex=1 := by
  simp [vertexSign,lastIndex,backwardSign]

theorem backward_sign_step (P : IntegerPartition) (q : ℕ → ℝ) (i : ℕ)
    (hi : i < P.m-1) :
    P.backwardSign q i=(if q i=-1 then 1 else -1)*P.backwardSign q (i+1) := by
  exact Finset.prod_eq_prod_Ico_succ_bot hi _

theorem vertex_parameters_recover (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.IsVertex q) (i : ℕ) (hi : i < P.m-1) :
    P.endpointParameters (P.vertexSign q) i=q i := by
  have him : i < P.m := by omega
  have hi1 : i+1 < P.m := by omega
  simp only [endpointParameters,signAt,dif_pos him,dif_pos hi1,vertexSign]
  rw [backward_sign_step P q i hi]
  rcases hq i hi with h | h <;>
    rcases backward_sign_pattern P q (i+1) with hb | hb <;> simp [h,hb] <;> norm_num

theorem every_vertex_determinant_cosine (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.IsVertex q) :
    (P.layerMatrix q).det=Real.cos (P.signedAngle (P.vertexSign q)) := by
  have he := layerMatrix_congr_parameters P (P.endpointParameters (P.vertexSign q)) q
    (vertex_parameters_recover P q hq)
  rw [← he]
  exact last_positive_layer_determinant P _ (vertex_sign_pattern P q) (vertex_sign_last P q)

theorem every_vertex_positive (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.IsVertex q) : 0 < (P.layerMatrix q).det := by
  rw [every_vertex_determinant_cosine P q hq]
  exact signed_angle_positive_cosine P _ (vertex_sign_pattern P q)

theorem every_nonpartition_vertex_bound (P : IntegerPartition) (hp : ¬P.HasPartition)
    (q : ℕ → ℝ) (hq : P.IsVertex q) :
    (P.layerMatrix q).det ≤ 1-(361/300)*(P.delta : ℝ)^2 := by
  rw [every_vertex_determinant_cosine P q hq]
  exact nonpartition_cosine_bound P _ (vertex_sign_pattern P q)
    (fun hw => hp ⟨P.vertexSign q,vertex_sign_pattern P q,hw⟩)

end IV04.Paper.IntegerPartition
