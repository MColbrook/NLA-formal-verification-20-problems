module

public import NLA.RA08.PaperNuclearBlockTrace
public import NLA.RA08.PaperNuclearTraceBounds
public import NLA.RA08.PaperNuclearTriangularLowerBound

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

/-- The exact lower bound in the manuscript, for its actual derivative family. -/
theorem nuclearDerivative_lower (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m+1)/Real.pi-1/2-Real.sqrt (2/15) ≤ nuclearNorm (nuclearDerivative m) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have ht := nuclearTriangular_nuclearNorm_lower m hm
  have hk := div_le_div_of_nonneg_right (nuclearKernel_polar_trace_lower m) hmpos.le
  have hd := nuclearDerivative_trace_lower m hm (nuclearTriangularPolar m)
    (nuclearTriangularPolar_unitary m)
  have he : (nuclearNorm (nuclearTriangular m)-(m : ℝ)/2-m*Real.sqrt (2/15))/(m : ℝ)=
      nuclearNorm (nuclearTriangular m)/(m : ℝ)-1/2-Real.sqrt (2/15) := by
    have hn := ne_of_gt hmpos
    field_simp
  rw [he] at hk
  linarith

theorem nuclearDerivative_unbounded (C : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ C < nuclearNorm (nuclearDerivative m) := by
  let X := Real.pi*(C+1/2+Real.sqrt (2/15))+1
  obtain ⟨m,hm⟩ := exists_nat_gt (max (1 : ℝ) (Real.exp X))
  have hmone : 1 ≤ m := by
    have h : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact_mod_cast h.le
  have hexp : Real.exp X < (m : ℝ)+1 := by
    have h := lt_of_le_of_lt (le_max_right _ _) hm
    linarith
  have hlog := Real.log_lt_log (Real.exp_pos X) hexp
  rw [Real.log_exp] at hlog
  have hdiv : C+1/2+Real.sqrt (2/15) < Real.log (m+1)/Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).mpr
    dsimp only [X] at hlog
    nlinarith
  have hl := nuclearDerivative_lower m hmone
  exact ⟨m,hmone,by linarith⟩

#print axioms nuclearDerivative_lower
#print axioms nuclearDerivative_unbounded
end NLA.RA08.Paper
