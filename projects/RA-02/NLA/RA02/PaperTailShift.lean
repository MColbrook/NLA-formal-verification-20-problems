module

public import NLA.RA02.PaperTailMinimizer
public import NLA.RA02.PaperTailScaling
public import NLA.RA02.PaperCorrelationRegularization

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem frame_identity_shift_trace {n q : ℕ} (A : NLA.RA02.Square n) (δ : ℝ)
    (U : Matrix (Fin n) (Fin q) ℂ) (hU : U.conjTranspose * U = 1) :
    (U.conjTranspose * (A+δ • 1) * U).trace.re =
      (U.conjTranspose * A * U).trace.re + δ*(q : ℝ) := by
  rw [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hU,Matrix.trace_add,Matrix.trace_smul,Complex.add_re]
  simp [Matrix.trace,Matrix.diag]

theorem rankTail_identity_shift {n : ℕ} (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (r : ℕ) (hr : r ≤ n) (δ : ℝ) (hδ : 0 ≤ δ) :
    NLA.RA02.rankTail (A+δ • 1) (hA.add (Matrix.PosSemidef.one.smul hδ)).isHermitian r =
      NLA.RA02.rankTail A hA.isHermitian r + δ*(n-r : ℕ) := by
  let B := A+δ • 1
  have hB : B.PosSemidef := hA.add (Matrix.PosSemidef.one.smul hδ)
  obtain ⟨U,hU,heU⟩ := exists_rankTail_minimizer A hA r hr
  obtain ⟨W,hW,heW⟩ := exists_rankTail_minimizer B hB r hr
  have hb := rankTail_le_compression_trace B hB r (le_refl _) U hU
  have ha := rankTail_le_compression_trace A hA r (le_refl _) W hW
  have hu := frame_identity_shift_trace A δ U hU
  have hw := frame_identity_shift_trace A δ W hW
  change (U.conjTranspose*B*U).trace.re = _ at hu
  change (W.conjTranspose*B*W).trace.re = _ at hw
  rw [heU] at hu
  rw [heW] at hw
  change NLA.RA02.rankTail B hB.isHermitian r = _
  linarith

theorem regularizedCorrelation_rankTail {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) (r : ℕ) (hr : r ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    NLA.RA02.rankTail (regularizedCorrelation C δ)
      (regularizedCorrelation_posDef C hC hδ).isHermitian r =
      (1+δ)⁻¹*(NLA.RA02.rankTail C hC.isHermitian r + δ*(n-r : ℕ)) := by
  have hd : 0 ≤ (1+δ)⁻¹ := inv_nonneg.mpr (by linarith)
  have he := rankTail_real_smul (1+δ)⁻¹ hd (C+δ • 1)
    (hC.add (Matrix.PosSemidef.one.smul hδ.le)) r
  change NLA.RA02.rankTail ((1+δ)⁻¹ • (C+δ • 1)) _ r = _
  rw [he,rankTail_identity_shift C hC r hr δ hδ.le]

#print axioms regularizedCorrelation_rankTail
end NLA.RA02.Paper
