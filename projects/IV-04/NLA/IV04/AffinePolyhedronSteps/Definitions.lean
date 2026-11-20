module

/- Actual finite real inequality systems; no vertex/certificate/runtime contracts. -/
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 def feasible {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i, (A *ᵥ x) i ≤ b i

 def feasibleSet {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) : Set (Fin n → ℝ) :=
  {x | feasible A b x}

 def tightRows {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (A *ᵥ x) i = b i)

 def lineFree {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) : Prop :=
  ∀ x d : Fin n → ℝ, (∀ t : ℝ, feasible A b (x+t • d)) → d=0

 theorem mem_tightRows {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ) (i : ι) :
    i ∈ tightRows A b x ↔ (A *ᵥ x) i = b i := by
  classical
  simp [tightRows]

 theorem tightRows_card_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ) :
    (tightRows A b x).card ≤ Fintype.card ι := by
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)

 theorem mulVec_shift {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (x d : Fin n → ℝ) (t : ℝ) (i : ι) :
    (A *ᵥ (x+t • d)) i = (A *ᵥ x) i+t*(A *ᵥ d) i := by
  simp [Matrix.mulVec_add, Matrix.mulVec_smul]

end
end Reference.IV04AffinePolyhedronSteps
