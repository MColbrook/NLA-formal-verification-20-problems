module

public import NLA.RA02.PaperLUVectorBound
public import NLA.RA03.Definitions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem lu_pivot_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (x : Fin n → ℂ) (i : Fin m) (j : Fin n) :
    NLA.RA03.pivotResidual A (i,j) *ᵥ x = vectorPivot (fun a => A a j) (A *ᵥ x) i := by
  by_cases hij : A i j = 0
  · simp [NLA.RA03.pivotResidual, vectorPivot, hij]
  · ext a
    simp only [NLA.RA03.pivotResidual, hij, if_false, vectorPivot,
      Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- Conditional row-pivot inequality for the actual complex LU residual.
It includes zero entries: their weight is zero without assuming all minors
or all entries are nonzero. No positive-definiteness assumption is needed. -/
theorem lu_conditional_vector_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (x : Fin n → ℂ) (j : Fin n) :
    (∑ i, Complex.normSq (A i j) *
      (∑ a, Complex.normSq ((NLA.RA03.pivotResidual A (i,j) *ᵥ x) a))) ≤
      2*(∑ i, Complex.normSq (A i j))*(∑ a, Complex.normSq ((A *ᵥ x) a)) -
        2*Complex.normSq (∑ i, star (A i j)*(A *ᵥ x) i) := by
  simp_rw [lu_pivot_mulVec]
  exact vectorPivot_weighted_bound (fun i => A i j) (A *ᵥ x)

#print axioms lu_conditional_vector_bound
end NLA.RA02.Paper
