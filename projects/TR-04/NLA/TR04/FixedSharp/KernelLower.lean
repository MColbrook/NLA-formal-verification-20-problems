module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.FixedSharp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A rank-deficient real matrix has a Euclidean unit vector in its kernel.
The basis argument follows the already verified RealSVD kernel-frame proof. -/
theorem exists_unit_kernel {n : ℕ} (B : Matrix ι (Fin n) ℝ) (hB : B.rank < n) :
    ∃ v : Fin n → ℝ, (∑ j, v j ^ 2) = 1 ∧ ∀ i, (∑ j, B i j * v j) = 0 := by
  let L := Matrix.toEuclideanLin B
  let K := LinearMap.ker L
  let b := stdOrthonormalBasis ℝ K
  have hRank : B.rank = Module.finrank ℝ (LinearMap.range L) := by
    exact Matrix.rank_eq_finrank_range_toLin B
      (PiLp.basisFun 2 ℝ ι) (PiLp.basisFun 2 ℝ (Fin n))
  have hdim := LinearMap.finrank_range_add_finrank_ker L
  rw [← hRank, finrank_euclideanSpace_fin] at hdim
  have hk : 0 < Module.finrank ℝ K := by dsimp [K]; omega
  let j : Fin (Module.finrank ℝ K) := ⟨0, hk⟩
  let v : Fin n → ℝ := fun k => (b j : EuclideanSpace ℝ (Fin n)) k
  refine ⟨v, ?_, ?_⟩
  · have hh : inner ℝ (b j) (b j) = 1 := by simpa using b.inner_eq_ite j j
    change (∑ k, v k * star (v k)) = 1 at hh
    simpa only [star_trivial, ← pow_two] using hh
  · intro i
    have hj : L (b j : EuclideanSpace ℝ (Fin n)) = 0 := (b j).property
    exact congrArg (fun v : EuclideanSpace ℝ ι => v i) hj

/-- An actual lower singular-energy bound forces a Frobenius error for every
matrix of deficient rank; no approximation or optimality witness is assumed. -/
theorem gram_lower_le_rank_error {n : ℕ} (A B : Matrix ι (Fin n) ℝ) (κ : ℝ)
    (hB : B.rank < n)
    (hA : ∀ v : Fin n → ℝ, κ * (∑ j, v j ^ 2) ≤ ∑ i, (∑ j, A i j * v j)^2) :
    κ ≤ ∑ i, ∑ j, (A i j - B i j)^2 := by
  obtain ⟨v, hv, hBv⟩ := exists_unit_kernel B hB
  have hlow := hA v
  rw [hv, mul_one] at hlow
  apply hlow.trans
  apply Finset.sum_le_sum
  intro i _
  have he : (∑ j, (A i j - B i j) * v j) = ∑ j, A i j * v j := by
    simp only [sub_mul, Finset.sum_sub_distrib, hBv i, sub_zero]
  have hi := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j - B i j) v
  rw [hv, mul_one, he] at hi
  exact hi

#print axioms exists_unit_kernel
#print axioms gram_lower_le_rank_error

end NLA.TR04.FixedSharp
