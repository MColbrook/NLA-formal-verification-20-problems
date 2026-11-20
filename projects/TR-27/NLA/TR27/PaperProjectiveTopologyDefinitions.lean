module

public import NLA.TR27.PaperCurveDefinitions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-- The usual quotient topology from the nonzero complex coordinate vectors.
This is defined independently of any particular curve or parametrization. -/
@[instance_reducible] def coordinateProjectiveTopology (n : ℕ) : TopologicalSpace (ℙ ℂ (Fin n → ℂ)) :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ)
    (inferInstance : TopologicalSpace {v : Fin n → ℂ // v ≠ 0})

def coordinateNormSq {n : ℕ} (v : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

/-- The Hermitian rank-one projector associated to a nonzero vector. Its
entries will separate projective points and establish Hausdorffness. -/
def coordinateProjector {n : ℕ} (v : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i j => v i * star (v j) / (coordinateNormSq v : ℂ)

def projectiveProjector {n : ℕ} (p : ℙ ℂ (Fin n → ℂ)) : Fin n → Fin n → ℂ :=
  coordinateProjector p.rep

end NLA.TR27.Paper
