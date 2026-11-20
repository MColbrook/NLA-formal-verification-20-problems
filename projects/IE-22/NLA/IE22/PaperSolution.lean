module

public import NLA.IE22.Final
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22.Paper
open NLA.IE21

theorem paper_canonical_sharp_constant (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    EventualUniformUpper θ (sharpConstant θ) ∧
    ∀ C : ℝ, C < sharpConstant θ → ¬EventualUniformUpper θ C := by
  exact NLA.IE22.canonical_sharp_constant θ hθ

theorem paper_high_aspect_supremum_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j => extremalValue θ (m j) (n j)) atTop (𝓝 (sharpConstant θ)) := by
  exact NLA.IE22.high_aspect_supremum_limit θ hθ m n hm hn hnlim hQlim

theorem paper_supremum_semantics (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (unitRowValues θ m n).Nonempty ∧ BddAbove (unitRowValues θ m n) ∧
    (∃ A : Mat m n, UnitRows A ∧ extremalValue θ m n = normalizedSingular θ A) ∧
    (∀ A : Mat m n, UnitRows A → normalizedSingular θ A ≤ extremalValue θ m n) ∧
    0 ≤ extremalValue θ m n ∧ extremalValue θ m n ≤ Real.sqrt n ∧
    ∀ A : Mat m n, 0 ≤ normalizedSingular θ A ∧
      normalizedSingular θ A ^ 2 = normalizedDeletion θ A := by
  exact NLA.IE22.supremum_semantics θ hθ m n hm hn

theorem paper_constant_semantics (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    0 ≤ sharpConstant θ ∧ sharpConstant θ ^ 2 = gaussianTrim θ ∧
    sharpConstant θ = Real.sqrt ((1 / Real.sqrt (2 * Real.pi)) *
      ∫ g in Icc (-gaussianCutoff θ) (gaussianCutoff θ), g ^ 2 * Real.exp (-(g ^ 2) / 2)) := by
  exact NLA.IE22.constant_semantics θ hθ

theorem paper_universal_squared_rate (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ m n : ℕ, 1 ≤ m → N ≤ n →
        (∀ A : Mat m n, UnitRows A →
          normalizedDeletion θ A ≤ gaussianTrim θ + C * errorSchedule n) ∧
        extremalValue θ m n ^ 2 ≤ gaussianTrim θ + C * errorSchedule n := by
  exact NLA.IE22.universal_squared_rate θ hθ

#print axioms paper_canonical_sharp_constant
#print axioms paper_high_aspect_supremum_limit
#print axioms paper_supremum_semantics
#print axioms paper_constant_semantics
#print axioms paper_universal_squared_rate

end NLA.IE22.Paper
