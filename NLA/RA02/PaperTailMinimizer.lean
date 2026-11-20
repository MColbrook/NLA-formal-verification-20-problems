module

public import NLA.RA02.PaperOneStepTail
public import NLA.RA02.PaperOrderedBasis

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

def pureTailFrame {n r : ℕ} (hr : r ≤ n) : Matrix (Fin n) (Fin (n-r)) ℂ :=
  fun i j => (Pi.single (tailIndex r hr j) (1 : ℂ) : Fin n → ℂ) i

theorem pureTailFrame_orthonormal {n r : ℕ} (hr : r ≤ n) :
    (pureTailFrame hr).conjTranspose * pureTailFrame hr = 1 := by
  ext i j
  simp [pureTailFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Pi.single_apply,
    apply_ite,(tailIndex_injective hr).eq_iff,Matrix.one_apply,eq_comm]

theorem pureTailFrame_trace {n r : ℕ} (hr : r ≤ n) (A : NLA.RA02.Square n) :
    ((pureTailFrame hr).conjTranspose * A * pureTailFrame hr).trace =
      ∑ j : Fin (n-r), A (tailIndex r hr j) (tailIndex r hr j) := by
  simp only [Matrix.trace,Matrix.diag]
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,pureTailFrame,Pi.single_apply,apply_ite]

theorem exists_rankTail_minimizer {n : ℕ} (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (r : ℕ) (hr : r ≤ n) :
    ∃ U : Matrix (Fin n) (Fin (n-r)) ℂ, U.conjTranspose * U = 1 ∧
      (U.conjTranspose * A * U).trace.re = NLA.RA02.rankTail A hA.isHermitian r := by
  obtain ⟨V,hdiag⟩ := exists_ordered_eigenbasis A hA.isHermitian
  let F := pureTailFrame hr
  have hV : (V : NLA.RA02.Square n).conjTranspose * (V : NLA.RA02.Square n) = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  refine ⟨(V : NLA.RA02.Square n)*F,?_,?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc
      _ = F.conjTranspose*((V : NLA.RA02.Square n).conjTranspose*(V : NLA.RA02.Square n))*F := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV,Matrix.mul_one]; exact pureTailFrame_orthonormal hr
  · have he : ((V : NLA.RA02.Square n)*F).conjTranspose*A*((V : NLA.RA02.Square n)*F) =
        F.conjTranspose*((V : NLA.RA02.Square n).conjTranspose*A*(V : NLA.RA02.Square n))*F := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [he,hdiag]
    change ((pureTailFrame hr).conjTranspose *
      Matrix.diagonal (fun i => (NLA.RA02.orderedEigenvalues A hA.isHermitian i : ℂ)) *
      pureTailFrame hr).trace.re = _
    rw [pureTailFrame_trace,Complex.re_sum]
    simp only [Matrix.diagonal_apply_eq,Complex.ofReal_re]
    exact sum_tailIndex hr _

#print axioms exists_rankTail_minimizer
end NLA.RA02.Paper
