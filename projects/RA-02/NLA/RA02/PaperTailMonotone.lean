module

public import NLA.RA02.PaperTailMinimizer
public import NLA.RA02.PaperGramRoot

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem frame_trace_le_realTrace {n q : ℕ} (A : NLA.RA02.Square n) (hA : A.PosSemidef)
    (U : Matrix (Fin n) (Fin q) ℂ) (hU : U.conjTranspose*U = 1) :
    (U.conjTranspose*A*U).trace.re ≤ NLA.RA02.realTrace A := by
  obtain ⟨S,hS⟩ := exists_gram_root A hA
  have hb := frobenius_compression_bound S U hU
  rw [lu_frobeniusSq_eq_gram_trace,hS] at hb
  exact hb

theorem frame_trace_mono {n q : ℕ} (A B : NLA.RA02.Square n)
    (hBA : (B-A).PosSemidef) (U : Matrix (Fin n) (Fin q) ℂ) :
    (U.conjTranspose*A*U).trace.re ≤ (U.conjTranspose*B*U).trace.re := by
  have hp := hBA.mul_mul_conjTranspose_same U.conjTranspose
  rw [Matrix.conjTranspose_conjTranspose] at hp
  have hn := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re] at hn
  exact sub_nonneg.mp hn

theorem rankTail_mono_psd {n : ℕ} (A B : NLA.RA02.Square n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hBA : (B-A).PosSemidef)
    (r : ℕ) (hr : r ≤ n) :
    NLA.RA02.rankTail A hA.isHermitian r ≤ NLA.RA02.rankTail B hB.isHermitian r := by
  obtain ⟨U,hU,he⟩ := exists_rankTail_minimizer B hB r hr
  exact (rankTail_le_compression_trace A hA r (le_refl _) U hU).trans
    ((frame_trace_mono A B hBA U).trans_eq he)

#print axioms rankTail_mono_psd
end NLA.RA02.Paper
