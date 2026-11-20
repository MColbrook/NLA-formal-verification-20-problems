module

public import NLA.MD06.BadOverlapExcess.Definitions
public import NLA.MD06.BadPatternCounts.PatternProperties

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadOverlap
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06BadPatternCounts
attribute [local instance] Classical.propDecidable

theorem actual_sorted_fin_pair_recovery {n : ℕ} (a b c d : Fin n)
    (hab : a < b) (hcd : c < d)
    (h : ({a,b} : Finset (Fin n)) = {c,d}) :
    a = c ∧ b = d := by
  have ha : a ∈ ({c,d} : Finset (Fin n)) := by rw [← h];simp
  have hb : b ∈ ({c,d} : Finset (Fin n)) := by rw [← h];simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · omega
  · exact ⟨ha,hb⟩
  · omega
  · omega

theorem actual_loop_pattern_injective (n : ℕ) :
    Function.Injective (LoopPattern (n := n)) := by
  intro x y h
  change {((x.1,x.2.val.1),(x.1,x.2.val.2))} =
    {((y.1,y.2.val.1),(y.1,y.2.val.2))} at h
  have he := Finset.singleton_inj.mp h
  apply Prod.ext
  · exact congrArg (fun e => e.1.1) he
  · apply Subtype.ext
    exact Prod.ext (congrArg (fun e => e.1.2) he) (congrArg (fun e => e.2.2) he)

theorem actual_double_vertex_image {n : ℕ} (d : DoubleDatum n) :
    (DoublePattern d).image (fun e => (e.1.1,e.2.1)) = {d.1.val} := by
  cases hb : d.2.2.2 <;> simp [DoublePattern,hb]

theorem actual_double_source_label_image {n : ℕ} (d : DoubleDatum n) :
    (DoublePattern d).image (fun e => e.1.2) = {d.2.1.val.1,d.2.1.val.2} := by
  cases hb : d.2.2.2 <;> simp [DoublePattern,hb]

theorem actual_double_target_label_image {n : ℕ} (d : DoubleDatum n) :
    (DoublePattern d).image (fun e => e.2.2) = {d.2.2.1.val.1,d.2.2.1.val.2} := by
  cases hb : d.2.2.2 with
  | false =>
    simp [DoublePattern,hb]
  | true =>
    simp only [DoublePattern,hb,if_true,Finset.image_insert,Finset.image_singleton]
    exact Finset.pair_comm _ _

theorem actual_two_matching_orientations_ne {n : ℕ} (u v : Fin n)
    (a b c d : Fin 3) (hab : a ≠ b) (hcd : c ≠ d) :
    ({((u,a),(v,c)),((u,b),(v,d))} : Finset (Dart n × Dart n)) ≠
      {((u,a),(v,d)),((u,b),(v,c))} := by
  intro h
  have he : ((u,a),(v,c)) ∈
      ({((u,a),(v,d)),((u,b),(v,c))} : Finset (Dart n × Dart n)) := by
    rw [← h]
    simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with he | he
  · exact hcd (congrArg (fun e => e.2.2) he)
  · exact hab (congrArg (fun e => e.1.2) he)

theorem actual_double_pattern_injective (n : ℕ) :
    Function.Injective (DoublePattern (n := n)) := by
  intro x y h
  have hv := congrArg (fun C : Finset (Dart n × Dart n) =>
    C.image (fun e => (e.1.1,e.2.1))) h
  rw [actual_double_vertex_image,actual_double_vertex_image] at hv
  have huv : x.1 = y.1 := Subtype.ext (Finset.singleton_inj.mp hv)
  have hs := congrArg (fun C : Finset (Dart n × Dart n) =>
    C.image (fun e => e.1.2)) h
  rw [actual_double_source_label_image,actual_double_source_label_image] at hs
  have hab := actual_sorted_fin_pair_recovery x.2.1.val.1 x.2.1.val.2
    y.2.1.val.1 y.2.1.val.2 x.2.1.property y.2.1.property hs
  have hs' : x.2.1 = y.2.1 := Subtype.ext (Prod.ext hab.1 hab.2)
  have ht := congrArg (fun C : Finset (Dart n × Dart n) =>
    C.image (fun e => e.2.2)) h
  rw [actual_double_target_label_image,actual_double_target_label_image] at ht
  have hcd := actual_sorted_fin_pair_recovery x.2.2.1.val.1 x.2.2.1.val.2
    y.2.2.1.val.1 y.2.2.1.val.2 x.2.2.1.property y.2.2.1.property ht
  have ht' : x.2.2.1 = y.2.2.1 := Subtype.ext (Prod.ext hcd.1 hcd.2)
  have hb : x.2.2.2 = y.2.2.2 := by
    cases hx : x.2.2.2 <;> cases hy : y.2.2.2
    · rfl
    · simp only [DoublePattern,hx,hy,Bool.false_eq_true,if_false,if_true,
        huv,hs',ht'] at h
      exact (actual_two_matching_orientations_ne y.1.val.1 y.1.val.2
        y.2.1.val.1 y.2.1.val.2 y.2.2.1.val.1 y.2.2.1.val.2
        (ne_of_lt y.2.1.property) (ne_of_lt y.2.2.1.property) h).elim
    · simp only [DoublePattern,hx,hy,Bool.false_eq_true,if_false,if_true,
        huv,hs',ht'] at h
      exact (actual_two_matching_orientations_ne y.1.val.1 y.1.val.2
        y.2.1.val.1 y.2.1.val.2 y.2.2.1.val.1 y.2.2.1.val.2
        (ne_of_lt y.2.1.property) (ne_of_lt y.2.2.1.property) h.symm).elim
    · rfl
  exact Prod.ext huv (Prod.ext hs' (Prod.ext ht' hb))

theorem actual_bad_pattern_injective (n : ℕ) :
    Function.Injective (BadPattern (n := n)) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (actual_loop_pattern_injective n h)
    | inr y =>
      have hc := congrArg Finset.card h
      simp only [BadPattern,actual_loop_pattern_card,actual_double_pattern_card] at hc
      omega
  | inr x =>
    cases y with
    | inl y =>
      have hc := congrArg Finset.card h
      simp only [BadPattern,actual_loop_pattern_card,actual_double_pattern_card] at hc
      omega
    | inr y => exact congrArg Sum.inr (actual_double_pattern_injective n h)

#print axioms actual_sorted_fin_pair_recovery
#print axioms actual_loop_pattern_injective
#print axioms actual_double_vertex_image
#print axioms actual_double_source_label_image
#print axioms actual_double_target_label_image
#print axioms actual_two_matching_orientations_ne
#print axioms actual_double_pattern_injective
#print axioms actual_bad_pattern_injective
end Reference.MD06BadOverlap
