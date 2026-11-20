module

public import NLA.MI22.Definitions
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Set
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace NLA.MI22.Paper

theorem scalar_power_increment (m α x e : ℝ) (hm : 0 < m)
    (hα : 0 < α) (hα1 : α < 1) (hx : m ≤ x) (he : 0 ≤ e) :
    (x+e)^α ≤ x^α + α*m^(α-1)*e := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z : ℝ => z^α) (f' := fun z => α*z^(α-1))
    (C := α*m^(α-1)) (s := Ici m)
    (fun z hz => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hm.trans_le hz)))).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hα.le (Real.rpow_nonneg (hm.trans_le hz).le _))]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hm hz (by linarith)) hα.le)
    (convex_Ici m) hx (show x+e ∈ Ici m by change m ≤ x+e; linarith)
  simp only [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg he] at h
  linarith [le_abs_self ((x+e)^α-x^α)]

section CStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem selfadjoint_norm_le {a : A} {r : ℝ} (ha : IsSelfAdjoint a)
    (hr : 0 ≤ r) (hl : algebraMap ℝ A (-r) ≤ a) (hu : a ≤ algebraMap ℝ A r) :
    ‖a‖ ≤ r := by
  obtain (h | h) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim a 0] using hr
  · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a ha with hpos | hneg
    · exact (le_algebraMap_iff_spectrum_le ha).mp hu _ hpos
    · have := (algebraMap_le_iff_le_spectrum ha).mp hl _ hneg
      linarith

theorem power_shift_upper (Q : A) (m α e : ℝ) (hm : 0 < m)
    (hα : 0 < α) (hα1 : α < 1) (he : 0 ≤ e)
    (hQ : IsSelfAdjoint Q) (hQ0 : 0 ≤ Q) (hQm : algebraMap ℝ A m ≤ Q) :
    CFC.rpow (Q+algebraMap ℝ A e) α ≤
      CFC.rpow Q α + algebraMap ℝ A (α*m^(α-1)*e) := by
  have heA : 0 ≤ algebraMap ℝ A e := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (smul_nonneg he (show (0 : A) ≤ 1 from zero_le_one))
  have hc : Continuous (fun x : ℝ => x^α) := Real.continuous_rpow_const hα.le
  have hshift : cfc (fun x : ℝ => (x+e)^α) Q = CFC.rpow (Q+algebraMap ℝ A e) α := by
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real (add_nonneg hQ0 heA)]
    have hh := cfc_comp (fun x : ℝ => x^α) (fun x => x+e) Q hQ
      hc.continuousOn (by fun_prop)
    have hid : cfc (fun x : ℝ => x+e) Q = Q+algebraMap ℝ A e := by
      rw [cfc_add_const e (fun x : ℝ => x) Q continuous_id.continuousOn hQ]
      rw [cfc_id' ℝ Q hQ]
    simpa only [Function.comp_def, hid] using hh
  rw [← hshift, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hQ0,
    ← cfc_add_const (α*m^(α-1)*e) (fun x : ℝ => x^α) Q hc.continuousOn hQ]
  apply (cfc_le_iff _ _ Q (hc.comp (continuous_id.add continuous_const)).continuousOn
    (hc.add continuous_const).continuousOn hQ).mpr
  intro x hx
  exact scalar_power_increment m α x e hm hα hα1
    ((algebraMap_le_iff_le_spectrum hQ).mp hQm x hx) he

theorem root_lipschitz_cstar (P Q : A) (m α : ℝ) (hm : 0 < m)
    (hα : 0 < α) (hα1 : α < 1) (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hPm : algebraMap ℝ A m ≤ P) (hQm : algebraMap ℝ A m ≤ Q) :
    ‖CFC.rpow P α-CFC.rpow Q α‖ ≤ α*m^(α-1)*‖P-Q‖ := by
  have hmA : 0 ≤ algebraMap ℝ A m := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (smul_nonneg hm.le (show (0 : A) ≤ 1 from zero_le_one))
  have hP0 := hmA.trans hPm
  have hQ0 := hmA.trans hQm
  have hup : P ≤ Q+algebraMap ℝ A ‖P-Q‖ := by
    have := IsSelfAdjoint.le_algebraMap_norm_self (P-Q) (hP.sub hQ)
    exact (sub_le_iff_le_add).mp this |>.trans_eq (add_comm _ _)
  have hdown : Q ≤ P+algebraMap ℝ A ‖P-Q‖ := by
    have := IsSelfAdjoint.le_algebraMap_norm_self (Q-P) (hQ.sub hP)
    rw [norm_sub_rev Q P] at this
    exact (sub_le_iff_le_add).mp this |>.trans_eq (add_comm _ _)
  have h1 := (CFC.rpow_le_rpow ⟨hα.le,hα1.le⟩ hup).trans
    (power_shift_upper Q m α ‖P-Q‖ hm hα hα1 (norm_nonneg _) hQ hQ0 hQm)
  have h2 := (CFC.rpow_le_rpow ⟨hα.le,hα1.le⟩ hdown).trans
    (power_shift_upper P m α ‖P-Q‖ hm hα hα1 (norm_nonneg _) hP hP0 hPm)
  apply selfadjoint_norm_le ((IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).sub
    (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg)) (by positivity)
  · rw [map_neg, neg_le_sub_iff_le_add]
    exact h2
  · exact sub_le_iff_le_add.mpr (h1.trans_eq (add_comm _ _))

end CStar

theorem root_lipschitz {n : ℕ} (P Q : Mat n) (m α : ℝ) (hm : 0 < m)
    (hα : 0 < α) (hα1 : α < 1) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPm : m • (1 : Mat n) ≤ P) (hQm : m • (1 : Mat n) ≤ Q) :
    operatorNorm (spectralPower P α-spectralPower Q α) ≤
      α*m^(α-1)*operatorNorm (P-Q) := by
  exact root_lipschitz_cstar P Q m α hm hα hα1 hP hQ
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hPm)
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hQm)

#print axioms root_lipschitz
end NLA.MI22.Paper
