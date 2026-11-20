module

public import NLA.MD06.FiniteProbability.Nonempty
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06FiniteProbability
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

theorem actual_counting_probability_nonnegative {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    0 ≤ countingProbability P := by
  unfold countingProbability
  positivity

theorem actual_counting_probability_monotone {Ω : Type*} [Fintype Ω]
    (P Q : Ω → Prop) (h : ∀ x, P x → Q x) :
    countingProbability P ≤ countingProbability Q := by
  unfold countingProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_subtype_mono P Q h

theorem actual_counting_probability_le_one {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) : countingProbability P ≤ 1 := by
  unfold countingProbability
  exact div_le_one_of_le₀ (by exact_mod_cast Fintype.card_subtype_le P)
    (Nat.cast_nonneg _)

theorem actual_counting_probability_union_bound {Ω : Type*} [Fintype Ω]
    (P Q : Ω → Prop) :
    countingProbability (fun x => P x ∨ Q x) ≤
      countingProbability P + countingProbability Q := by
  classical
  unfold countingProbability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_cast
  simp only [Fintype.card_subtype]
  calc
    _ = ((Finset.univ.filter P) ∪ (Finset.univ.filter Q)).card := by
      congr 1
      ext x
      simp
    _ ≤ _ := Finset.card_union_le _ _

theorem actual_counting_probability_three_union_bound {Ω : Type*} [Fintype Ω]
    (P Q T : Ω → Prop) :
    countingProbability (fun x => (P x ∨ Q x) ∨ T x) ≤
      countingProbability P + countingProbability Q + countingProbability T := by
  have h1 := actual_counting_probability_union_bound (fun x => P x ∨ Q x) T
  have h2 := actual_counting_probability_union_bound P Q
  linarith

theorem actual_counting_probability_complement {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) :
    countingProbability (fun x => ¬P x) = 1-countingProbability P := by
  classical
  have hc := Fintype.card_subtype_le P
  have hden : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Fintype.card_pos)
  unfold countingProbability
  rw [Fintype.card_subtype_compl, Nat.cast_sub hc]
  field_simp

theorem actual_graph_probability_sample_formula (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) :
    GraphProbability k P = countingProbability (fun G : CubicSample k => P G.val) := by
  classical
  let e : {G : SimpleGraph (Fin (Size k)) // G.IsRegularOfDegree 3 ∧ P G} ≃
      {G : CubicSample k // P G.val} :=
    { toFun := fun G => ⟨⟨G.val,G.property.1⟩,G.property.2⟩
      invFun := fun G => ⟨G.val.val,⟨G.val.property,G.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold GraphProbability countingProbability
  rw [Fintype.card_congr e]

theorem actual_uniform_cubic_event_mass (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) :
    (UniformCubic k).toOuterMeasure {G : CubicSample k | P G.val} =
      (Fintype.card {G : CubicSample k // P G.val} : ℝ≥0∞) /
        (Fintype.card (CubicSample k) : ℝ≥0∞) := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp only [Set.indicator_apply, UniformCubic, PMF.ofFintype_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype, div_eq_mul_inv, Set.mem_setOf_eq]

theorem actual_graph_probability_uniform_real (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) :
    ((UniformCubic k).toOuterMeasure {G : CubicSample k | P G.val}).toReal =
      GraphProbability k P := by
  rw [actual_uniform_cubic_event_mass, actual_graph_probability_sample_formula]
  simp [ENNReal.toReal_div, countingProbability]

theorem actual_graph_probability_three_union_bound (k : ℕ)
    (P Q T : SimpleGraph (Fin (Size k)) → Prop) :
    GraphProbability k (fun G => (P G ∨ Q G) ∨ T G) ≤
      GraphProbability k P+GraphProbability k Q+GraphProbability k T := by
  simp only [actual_graph_probability_sample_formula]
  exact actual_counting_probability_three_union_bound _ _ _

theorem actual_graph_probability_complement (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) :
    GraphProbability k (fun G => ¬P G) = 1-GraphProbability k P := by
  simp only [actual_graph_probability_sample_formula]
  exact actual_counting_probability_complement _

theorem actual_graph_failure_probability_bound (k : ℕ)
    (Success P Q T : SimpleGraph (Fin (Size k)) → Prop)
    (h : ∀ G, G.IsRegularOfDegree 3 → P G → Q G → T G → Success G) :
    GraphProbability k (fun G => ¬Success G) ≤
      GraphProbability k (fun G => ¬P G) +
        GraphProbability k (fun G => ¬Q G) + GraphProbability k (fun G => ¬T G) := by
  simp only [actual_graph_probability_sample_formula]
  apply le_trans (actual_counting_probability_monotone
    (fun G : CubicSample k => ¬Success G.val)
    (fun G => (¬P G.val ∨ ¬Q G.val) ∨ ¬T G.val) _) _
  · intro G hn
    by_contra he
    apply hn
    exact h G.val G.property (by tauto) (by tauto) (by tauto)
  · exact actual_counting_probability_three_union_bound _ _ _

end Reference.MD06FiniteProbability
#print axioms Reference.MD06FiniteProbability.actual_counting_probability_nonnegative
#print axioms Reference.MD06FiniteProbability.actual_counting_probability_monotone
#print axioms Reference.MD06FiniteProbability.actual_counting_probability_le_one
#print axioms Reference.MD06FiniteProbability.actual_counting_probability_union_bound
#print axioms Reference.MD06FiniteProbability.actual_counting_probability_three_union_bound
#print axioms Reference.MD06FiniteProbability.actual_counting_probability_complement
#print axioms Reference.MD06FiniteProbability.actual_graph_probability_sample_formula
#print axioms Reference.MD06FiniteProbability.actual_uniform_cubic_event_mass
#print axioms Reference.MD06FiniteProbability.actual_graph_probability_uniform_real
#print axioms Reference.MD06FiniteProbability.actual_graph_probability_three_union_bound
#print axioms Reference.MD06FiniteProbability.actual_graph_probability_complement
#print axioms Reference.MD06FiniteProbability.actual_graph_failure_probability_bound
