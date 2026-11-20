module

public import NLA.IE21.PaperLimits
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21.Paper
open NLA.IE21

theorem paper_random_rows (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ)/n j) atTop atTop)
    (Ω : ℕ → Type*) [∀ j, MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (A : (j : ℕ) → Ω j → Mat (m j) (n j))
    (hA : ∀ j, IndependentSphereRows (μ j) (A j)) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => (μ j).real
      {ω | ¬(|normalizedDeletion θ (A j ω)-gaussianTrim θ| ≤ η ∧
        |normalizedOperator (A j ω)-1| ≤ η ∧ |deletionRatio θ (A j ω)-gaussianTrim θ| ≤ η)})
      atTop (𝓝 0) := by
  exact original_joint_limit θ hθ m n hm hn hnlim hQlim Ω μ A hA η hη

theorem paper_gaussian_constant (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    0 < gaussianCutoff θ ∧
    (gaussianReal 0 1).real {g | |g| ≤ gaussianCutoff θ} = θ ∧
    (∀ a : ℝ, 0 < a → (gaussianReal 0 1).real {g | |g| ≤ a} = θ →
      a = gaussianCutoff θ) ∧
    gaussianTrim θ = ∫ g in {g | |g| ≤ gaussianCutoff θ}, g ^ 2 ∂gaussianReal 0 1 ∧
    0 ≤ gaussianTrim θ ∧ gaussianTrim θ ≤ 1 := by
  exact NLA.IE21.gaussian_constant θ hθ

theorem paper_deletion_minimum {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hn : 1 ≤ n) :
    0 ≤ deletionSingular θ A ∧
    (∃ (S : Finset (Fin m)) (x : Space n),
      S.card = retainedRows θ m ∧ ‖x‖ = 1 ∧
      deletionSingular θ A = retainedNorm A S x) ∧
    (∀ (S : Finset (Fin m)) (x : Space n),
      S.card = retainedRows θ m → ‖x‖ = 1 →
      deletionSingular θ A ≤ retainedNorm A S x) := by
  exact NLA.IE21.deletion_minimum θ hθ A hn

#print axioms paper_random_rows
#print axioms paper_gaussian_constant
#print axioms paper_deletion_minimum

end NLA.IE21.Paper
