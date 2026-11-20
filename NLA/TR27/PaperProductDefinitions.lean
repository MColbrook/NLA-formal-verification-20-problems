module

public import NLA.TR27.Definitions
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem tensor_reps_nonzero (k : ℕ) (q : Fin k → ℙ ℂ W) :
    PiTensorProduct.tprod ℂ (fun i => (q i).rep) ≠ 0 := by
  classical
  choose f hf using fun i => Module.Projective.exists_dual_eq_one ℂ (q i).rep_nonzero
  let F : (⨂[ℂ] _ : Fin k, W) →ₗ[ℂ] ℂ :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compLinearMap f)
  intro hz
  have h := congrArg F hz
  simpa [F, hf] using h

def tensorPoint (k : ℕ) (q : Fin k → ℙ ℂ W) : ℙ ℂ (⨂[ℂ] _ : Fin k, W) :=
  Projectivization.mk ℂ (PiTensorProduct.tprod ℂ (fun i => (q i).rep)) (tensor_reps_nonzero k q)

def powerPoint (p : ℙ ℂ W) (k : ℕ) : ℙ ℂ (⨂[ℂ] _ : Fin k, W) :=
  tensorPoint k (fun _ => p)

/-- Full Segre product, with separately and freely selected projective factors. -/
def productPoints (X : Set (ℙ ℂ W)) (k : ℕ) : Set (ℙ ℂ (⨂[ℂ] _ : Fin k, W)) :=
  {z | ∃ q : Fin k → ℙ ℂ W, (∀ i, q i ∈ X) ∧
    Represents (PiTensorProduct.tprod ℂ (fun i => (q i).rep)) z}

end NLA.TR27.Paper
