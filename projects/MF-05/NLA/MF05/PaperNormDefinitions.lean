module

public import NLA.MF05.PaperGrowthDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper

def IsRealNorm {d : ℕ} (p : RealVector d → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∀ x, p x = 0 ↔ x = 0) ∧
  (∀ x y, p (x+y) ≤ p x+p y) ∧ (∀ c : ℝ, ∀ x, p (c • x) = ‖c‖*p x)

/-- The induced operator norm, as the supremum over every nonzero vector. -/
def inducedNorm {E : Type*} [Zero E] (p : E → ℝ) (f : E → E) : ℝ :=
  sSup {r : ℝ | ∃ x : E, x ≠ 0 ∧ r = p (f x)/p x}

/-- The literal unit-sphere supremum divided by the unit-sphere infimum. -/
def eccentricity {E : Type*} [Norm E] (p : E → ℝ) : ℝ :=
  sSup (p '' {x : E | ‖x‖ = 1}) / sInf (p '' {x : E | ‖x‖ = 1})

end NLA.MF05.Paper
