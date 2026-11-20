module

public import NLA.RA02.PaperCorrelationDefinitions
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
namespace NLA.RA02.Paper

theorem regularizedCorrelation_posDef {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) {δ : ℝ} (hδ : 0 < δ) : (regularizedCorrelation C δ).PosDef := by
  have hI : (δ • (1 : NLA.RA02.Square n)).PosDef := Matrix.PosDef.one.smul hδ
  exact (Matrix.PosDef.posSemidef_add hC hI).smul (inv_pos.mpr (by linarith : 0 < 1+δ))

theorem regularizedCorrelation_unitDiagonal {n : ℕ} (C : NLA.RA02.Square n)
    (hd : ∀ i, C i i = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ i, regularizedCorrelation C δ i i = 1 := by
  intro i
  have hne : 1+δ ≠ 0 := ne_of_gt (by linarith : 0 < 1+δ)
  simp only [regularizedCorrelation,Matrix.smul_apply,Matrix.add_apply,hd,Matrix.one_apply,if_pos rfl]
  apply Complex.ext <;> simp only [Complex.smul_re,Complex.smul_im,Complex.add_re,Complex.add_im,
    ite_true,Complex.one_re,Complex.one_im,smul_eq_mul,mul_one,mul_zero,add_zero]
  exact inv_mul_cancel₀ hne

theorem regularizedCorrelation_realPositive {n : ℕ} (C : NLA.RA02.Square n)
    (hc : ∀ i j, (C i j).im = 0 ∧ 0 < (C i j).re) {δ : ℝ} (hδ : 0 < δ) :
    ∀ i j, (regularizedCorrelation C δ i j).im = 0 ∧ 0 < (regularizedCorrelation C δ i j).re := by
  intro i j
  have hden : 0 < (1+δ)⁻¹ := inv_pos.mpr (by linarith : 0 < 1+δ)
  by_cases hij : i=j
  · subst j
    constructor
    · simp only [regularizedCorrelation,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,
        ite_true,Complex.smul_im,Complex.add_im,Complex.one_im,(hc i i).1,smul_eq_mul,mul_zero,add_zero]
    · simpa only [regularizedCorrelation,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,
        ite_true,Complex.smul_re,Complex.add_re,Complex.one_re,smul_eq_mul,mul_one]
        using mul_pos hden (add_pos (hc i i).2 hδ)
  · constructor
    · simp only [regularizedCorrelation,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,
        if_neg hij,Complex.smul_im,Complex.add_im,Complex.zero_im,(hc i j).1,smul_eq_mul,mul_zero,add_zero]
    · simpa only [regularizedCorrelation,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,
        if_neg hij,Complex.smul_re,Complex.add_re,Complex.zero_re,smul_eq_mul,mul_zero,add_zero]
        using mul_pos hden (hc i j).2

theorem regularizedCorrelation_continuousAt_zero {n : ℕ} (C : NLA.RA02.Square n) :
    ContinuousAt (regularizedCorrelation C) 0 := by
  have hs : ContinuousAt (fun δ : ℝ => (1+δ)⁻¹) 0 :=
    (continuousAt_const.add continuousAt_id).inv₀ (by norm_num)
  exact hs.smul (continuousAt_const.add (continuousAt_id.smul continuousAt_const))

theorem regularizedCorrelation_tendsto_zero {n : ℕ} (C : NLA.RA02.Square n) :
    Filter.Tendsto (regularizedCorrelation C) (𝓝 0) (𝓝 C) := by
  simpa [regularizedCorrelation] using (regularizedCorrelation_continuousAt_zero C).tendsto

#print axioms regularizedCorrelation_tendsto_zero
end NLA.RA02.Paper
