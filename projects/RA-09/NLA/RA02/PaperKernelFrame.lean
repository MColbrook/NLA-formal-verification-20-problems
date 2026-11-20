module

public import NLA.RA02.PaperFrobeniusCompression
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem exists_kernel_frame {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) (hr : B.rank ≤ r) :
    ∃ (q : ℕ) (U : Matrix (Fin n) (Fin q) ℂ), n-r ≤ q ∧ U.conjTranspose*U = 1 ∧ B*U = 0 := by
  let L := Matrix.toEuclideanLin B
  let K := LinearMap.ker L
  let q := Module.finrank ℂ K
  let b := stdOrthonormalBasis ℂ K
  let U : Matrix (Fin n) (Fin q) ℂ := fun i j => (b j : EuclideanSpace ℂ (Fin n)) i
  have hRank : B.rank = Module.finrank ℂ (LinearMap.range L) := by
    exact Matrix.rank_eq_finrank_range_toLin B (PiLp.basisFun 2 ℂ (Fin m)) (PiLp.basisFun 2 ℂ (Fin n))
  have hdim := LinearMap.finrank_range_add_finrank_ker L
  rw [← hRank, finrank_euclideanSpace_fin] at hdim
  refine ⟨q,U,?_,?_,?_⟩
  · change n-r ≤ Module.finrank ℂ (LinearMap.ker L)
    omega
  · ext j l
    have hinner := b.inner_eq_ite j l
    have he : (U.conjTranspose*U) j l = inner ℂ (b j) (b l) := by
      change (∑ i, star ((b j : EuclideanSpace ℂ (Fin n)) i) * (b l : EuclideanSpace ℂ (Fin n)) i) =
        ∑ i, (b l : EuclideanSpace ℂ (Fin n)) i * star ((b j : EuclideanSpace ℂ (Fin n)) i)
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he,hinner]
    rfl
  · ext i j
    have hj : L (b j : EuclideanSpace ℂ (Fin n)) = 0 := (b j).property
    have he := congrArg (fun v : EuclideanSpace ℂ (Fin m) => v i) hj
    exact he

#print axioms exists_kernel_frame
end NLA.RA02.Paper
