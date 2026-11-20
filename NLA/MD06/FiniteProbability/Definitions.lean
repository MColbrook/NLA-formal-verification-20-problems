module

public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06FiniteProbability
open scoped BigOperators
open SimpleGraph
attribute [local instance] Classical.propDecidable

abbrev Size (k : ℕ) : ℕ := 2*(k+2)

abbrev CubicSample (k : ℕ) :=
  {G : SimpleGraph (Fin (Size k)) // G.IsRegularOfDegree 3}

noncomputable instance sampleFintype (k : ℕ) : Fintype (CubicSample k) :=
  Fintype.ofFinite _

noncomputable def countingProbability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ :=
  (Fintype.card {x : Ω // P x} : ℝ)/(Fintype.card Ω : ℝ)

noncomputable def GraphProbability (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) : ℝ :=
  (Fintype.card {G : SimpleGraph (Fin (Size k)) // G.IsRegularOfDegree 3 ∧ P G} : ℝ) /
    (Fintype.card (CubicSample k) : ℝ)

def Prism (k : ℕ) : SimpleGraph (Fin (2*(k+3))) :=
  ((⊤ : SimpleGraph (Fin 2)) □ cycleGraph (k+3)).comap
    (finProdFinEquiv : Fin 2 × Fin (k+3) ≃ Fin (2*(k+3))).symm

end Reference.MD06FiniteProbability
