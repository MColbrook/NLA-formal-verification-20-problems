module

public import NLA.RA09.PaperDefinitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

/-! Power functions in the manuscript's full scalar class. -/
set_option autoImplicit false
noncomputable section
namespace NLA.RA09.Paper

theorem power_admissible {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    PaperAdmissibleFunction (fun x : ℝ => x ^ p) := by
  refine ⟨(Real.continuous_rpow_const hp.le).continuousOn,
    Real.monotoneOn_rpow_Ici_of_exponent_nonneg hp.le,
    fun x hx => Real.rpow_nonneg hx p, ?_⟩
  intro x y hx hxy
  rw [← Real.rpow_sub_one (ne_of_gt hx),
    ← Real.rpow_sub_one (ne_of_gt (hx.trans_le hxy))]
  exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (sub_nonpos.mpr hp1)
    hx (hx.trans_le hxy) hxy

#print axioms power_admissible

end NLA.RA09.Paper

