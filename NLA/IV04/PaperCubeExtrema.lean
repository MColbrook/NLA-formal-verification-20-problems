module

public import NLA.IV04.PaperCubeAffinity

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper

/-- Replacing finitely many independent affine coordinates by endpoints can
only increase the value. The endpoint choices are constructed in the proof. -/
theorem affine_cube_vertex_above {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : (ι → ℝ) → ℝ)
    (haff : ∀ q i, i ∈ S → ∀ t : ℝ,
      f (Function.update q i t)=((1-t)/2)*f (Function.update q i (-1))+
        ((1+t)/2)*f (Function.update q i 1))
    (q : ι → ℝ) (hq : ∀ i ∈ S, -1 ≤ q i ∧ q i ≤ 1) :
    ∃ r : ι → ℝ, (∀ i ∈ S, r i=-1 ∨ r i=1) ∧
      (∀ i ∉ S, r i=q i) ∧ f q ≤ f r := by
  classical
  induction S using Finset.induction_on generalizing q with
  | empty => exact ⟨q,by simp,by simp,le_rfl⟩
  | @insert a S ha ih =>
    have hqa := hq a (Finset.mem_insert_self a S)
    have he := haff q a (Finset.mem_insert_self a S) (q a)
    rw [Function.update_eq_self] at he
    have hend : ∃ t : ℝ, (t=-1 ∨ t=1) ∧ f q ≤ f (Function.update q a t) := by
      by_cases h : f (Function.update q a (-1)) ≤ f (Function.update q a 1)
      · refine ⟨1,Or.inr rfl,?_⟩
        nlinarith [mul_nonneg (show 0 ≤ (1-q a)/2 by linarith) (sub_nonneg.mpr h)]
      · refine ⟨-1,Or.inl rfl,?_⟩
        have hb := le_of_lt (lt_of_not_ge h)
        nlinarith [mul_nonneg (show 0 ≤ (1+q a)/2 by linarith) (sub_nonneg.mpr hb)]
    obtain ⟨t,ht,hft⟩ := hend
    have hq' : ∀ i ∈ S, -1 ≤ (Function.update q a t) i ∧ (Function.update q a t) i ≤ 1 := by
      intro i hi
      have hia : i ≠ a := by intro he; subst i; exact ha hi
      rw [Function.update_of_ne hia]
      exact hq i (Finset.mem_insert_of_mem hi)
    have haff' : ∀ q i, i ∈ S → ∀ t : ℝ,
        f (Function.update q i t)=((1-t)/2)*f (Function.update q i (-1))+
          ((1+t)/2)*f (Function.update q i 1) := by
      intro q i hi t
      exact haff q i (Finset.mem_insert_of_mem hi) t
    obtain ⟨r,hrv,hre,hfr⟩ := ih haff' (Function.update q a t) hq'
    refine ⟨r,?_,?_,hft.trans hfr⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with hia | hi
      · subst i
        rw [hre a ha,Function.update_self]
        exact ht
      · exact hrv i hi
    · intro i hi
      have hiS : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
      have hia : i ≠ a := by intro h; subst i; exact hi (Finset.mem_insert_self a S)
      rw [hre i hiS,Function.update_of_ne hia]

theorem affine_cube_vertex_below {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : (ι → ℝ) → ℝ)
    (haff : ∀ q i, i ∈ S → ∀ t : ℝ,
      f (Function.update q i t)=((1-t)/2)*f (Function.update q i (-1))+
        ((1+t)/2)*f (Function.update q i 1))
    (q : ι → ℝ) (hq : ∀ i ∈ S, -1 ≤ q i ∧ q i ≤ 1) :
    ∃ r : ι → ℝ, (∀ i ∈ S, r i=-1 ∨ r i=1) ∧
      (∀ i ∉ S, r i=q i) ∧ f r ≤ f q := by
  have hneg : ∀ q i, i ∈ S → ∀ t : ℝ,
      -f (Function.update q i t)=((1-t)/2)*(-f (Function.update q i (-1)))+
        ((1+t)/2)*(-f (Function.update q i 1)) := by
    intro q i hi t
    rw [haff q i hi t]
    ring
  obtain ⟨r,hrv,hre,hfr⟩ := affine_cube_vertex_above S (fun q => -f q) hneg q hq
  exact ⟨r,hrv,hre,by linarith⟩

namespace IntegerPartition

theorem determinant_vertex_above (P : IntegerPartition) (q : ℕ → ℝ) (hq : P.InCube q) :
    ∃ r : ℕ → ℝ, P.IsVertex r ∧ (P.layerMatrix q).det ≤ (P.layerMatrix r).det := by
  obtain ⟨r,hrv,_,hfr⟩ := affine_cube_vertex_above (Finset.range (P.m-1))
    (fun q => (P.layerMatrix q).det)
    (fun q i hi t => determinant_parameter_interpolation P q ⟨i,Finset.mem_range.mp hi⟩ t)
    q (fun i hi => hq i (Finset.mem_range.mp hi))
  exact ⟨r,fun i hi => hrv i (Finset.mem_range.mpr hi),hfr⟩

theorem determinant_vertex_below (P : IntegerPartition) (q : ℕ → ℝ) (hq : P.InCube q) :
    ∃ r : ℕ → ℝ, P.IsVertex r ∧ (P.layerMatrix r).det ≤ (P.layerMatrix q).det := by
  obtain ⟨r,hrv,_,hfr⟩ := affine_cube_vertex_below (Finset.range (P.m-1))
    (fun q => (P.layerMatrix q).det)
    (fun q i hi t => determinant_parameter_interpolation P q ⟨i,Finset.mem_range.mp hi⟩ t)
    q (fun i hi => hq i (Finset.mem_range.mp hi))
  exact ⟨r,fun i hi => hrv i (Finset.mem_range.mpr hi),hfr⟩

theorem all_parameter_determinant_positive (P : IntegerPartition) (q : ℕ → ℝ)
    (hq : P.InCube q) : 0 < (P.layerMatrix q).det := by
  obtain ⟨r,hr,hb⟩ := determinant_vertex_below P q hq
  exact lt_of_lt_of_le (every_vertex_positive P r hr) hb

theorem all_nonpartition_determinant_bound (P : IntegerPartition) (hp : ¬P.HasPartition)
    (q : ℕ → ℝ) (hq : P.InCube q) :
    (P.layerMatrix q).det ≤ 1-(361/300)*(P.delta : ℝ)^2 := by
  obtain ⟨r,hr,hb⟩ := determinant_vertex_above P q hq
  exact hb.trans (every_nonpartition_vertex_bound P hp r hr)

theorem partition_determinant_threshold (P : IntegerPartition) :
    P.HasPartition ↔ ∃ q : ℕ → ℝ, P.InCube q ∧
      (P.threshold : ℝ) ≤ (P.layerMatrix q).det := by
  constructor
  · intro hp
    obtain ⟨sign,_,_,hq,hdet⟩ := partition_layer_threshold_witness P hp
    refine ⟨P.endpointParameters sign,?_,hdet⟩
    intro i _
    rcases hq i with h | h <;> simp [h]
  · rintro ⟨q,hq,hdet⟩
    by_contra hp
    have hb := all_nonpartition_determinant_bound P hp q hq
    have hd : (0 : ℝ) < P.delta := by exact_mod_cast delta_pos P
    simp only [threshold,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at hdet
    nlinarith [sq_pos_of_pos hd]

end IntegerPartition
end IV04.Paper
