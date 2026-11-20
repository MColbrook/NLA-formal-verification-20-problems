module

public import NLA.RA02.PaperKyFan

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

def tailIndex {n : ℕ} (k : ℕ) (hk : k ≤ n) (j : Fin (n-k)) : Fin n :=
  ⟨k+j.val, by omega⟩

theorem tailIndex_injective {n k : ℕ} (hk : k ≤ n) : Function.Injective (tailIndex k hk) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg Fin.val hij
  change k+i.val=k+j.val at he
  omega

def headTailFrame {n k : ℕ} (hk : k ≤ n) (g : Fin n → ℂ) :
    Matrix (Fin n) (Fin (n-k+1)) ℂ :=
  fun i => Fin.cons (g i) (fun j => (Pi.single (tailIndex k hk j) (1 : ℂ) : Fin n → ℂ) i)

theorem headTailFrame_orthonormal {n k : ℕ} (hk : k ≤ n) (g : Fin n → ℂ)
    (hg : ∀ i, k ≤ i.val → g i = 0) (hnorm : ∑ i, Complex.normSq (g i) = 1) :
    (headTailFrame hk g).conjTranspose * headTailFrame hk g = 1 := by
  have htail : ∀ j, g (tailIndex k hk j) = 0 := fun j => hg _ (by simp [tailIndex])
  have hn : (∑ i, star (g i)*g i) = (1 : ℂ) := by
    have hh := congrArg Complex.ofReal hnorm
    simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Complex.star_def, Complex.ofReal_one] using hh
  ext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simpa [headTailFrame,Matrix.mul_apply,Matrix.conjTranspose_apply] using hn
    | succ j =>
      simp [headTailFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Pi.single_apply,htail,Matrix.one_apply,eq_comm]
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simp [headTailFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Pi.single_apply,htail,apply_ite]
    | succ j =>
      simp [headTailFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Pi.single_apply,apply_ite,
        (tailIndex_injective hk).eq_iff,Matrix.one_apply,eq_comm]

theorem headTailFrame_trace {n k : ℕ} (hk : k ≤ n) (g : Fin n → ℂ) (R : NLA.RA02.Square n) :
    ((headTailFrame hk g).conjTranspose * R * headTailFrame hk g).trace =
      star g ⬝ᵥ (R *ᵥ g) + ∑ j : Fin (n-k), R (tailIndex k hk j) (tailIndex k hk j) := by
  simp only [Matrix.trace,Matrix.diag,Fin.sum_univ_succ]
  congr 1
  · simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,headTailFrame,Fin.cons_zero]
    simp only [dotProduct,Matrix.mulVec]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.star_apply]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,headTailFrame,Pi.single_apply,apply_ite]

theorem rankTail_le_headTail_probe {n k : ℕ} (hk : k ≤ n) (hkpos : 1 ≤ k)
    (R : NLA.RA02.Square n) (hR : R.PosSemidef)
    (V : Matrix.unitaryGroup (Fin n) ℂ) (g : Fin n → ℂ)
    (hg : ∀ i, k ≤ i.val → g i = 0) (hnorm : ∑ i, Complex.normSq (g i) = 1) :
    NLA.RA02.rankTail R hR.isHermitian (k-1) ≤
      (star g ⬝ᵥ (((V : NLA.RA02.Square n).conjTranspose*R*(V : NLA.RA02.Square n)) *ᵥ g) +
        ∑ j : Fin (n-k), ((V : NLA.RA02.Square n).conjTranspose*R*(V : NLA.RA02.Square n))
          (tailIndex k hk j) (tailIndex k hk j)).re := by
  let F := headTailFrame hk g
  have hV : (V : NLA.RA02.Square n).conjTranspose*(V : NLA.RA02.Square n) = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hU : ((V : NLA.RA02.Square n)*F).conjTranspose*((V : NLA.RA02.Square n)*F) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = F.conjTranspose*((V : NLA.RA02.Square n).conjTranspose*(V : NLA.RA02.Square n))*F := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV,Matrix.mul_one]; exact headTailFrame_orthonormal hk g hg hnorm
  have hb := rankTail_le_compression_trace R hR (k-1) (show n-(k-1) ≤ n-k+1 by omega)
    ((V : NLA.RA02.Square n)*F) hU
  have he : ((V : NLA.RA02.Square n)*F).conjTranspose*R*((V : NLA.RA02.Square n)*F) =
      F.conjTranspose*((V : NLA.RA02.Square n).conjTranspose*R*(V : NLA.RA02.Square n))*F := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [he,headTailFrame_trace] at hb
  exact hb

#print axioms rankTail_le_headTail_probe
end NLA.RA02.Paper
