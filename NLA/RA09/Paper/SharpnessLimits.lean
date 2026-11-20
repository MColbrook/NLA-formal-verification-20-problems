module

public import NLA.RA09.Paper.Powers
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! The simultaneous sharpness limit from the paper, with L tending to infinity.
The matrix realization is a separate obligation. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace NLA.RA09.Paper

def inputExcess (L : ℝ) : ℝ := 1 + Real.exp (-L)^2
def outputExcess (L : ℝ) : ℝ := 1 + Real.exp (-(1/L))^2
def squaredExcessRatio (L : ℝ) : ℝ := outputExcess L / inputExcess L
def normExcessRatio (L : ℝ) : ℝ :=
  (Real.sqrt (1 + outputExcess L / L) - 1) /
    (Real.sqrt (1 + inputExcess L / L) - 1)

theorem inputExcess_pos (L : ℝ) : 0 < inputExcess L := by
  unfold inputExcess
  positivity

theorem outputExcess_pos (L : ℝ) : 0 < outputExcess L := by
  unfold outputExcess
  positivity

theorem inputExcess_limit : Tendsto inputExcess atTop (𝓝 1) := by
  unfold inputExcess
  simpa [inputExcess] using tendsto_const_nhds.add
    (Real.tendsto_exp_neg_atTop_nhds_zero.pow 2)

theorem outputExcess_limit : Tendsto outputExcess atTop (𝓝 2) := by
  unfold outputExcess
  have hi : Tendsto (fun L : ℝ => 1/L) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have he := Real.continuous_exp.continuousAt.tendsto.comp hi.neg
  convert (tendsto_const_nhds (x := (1 : ℝ))).add (he.pow 2) using 1 <;> norm_num

theorem squaredExcessRatio_limit : Tendsto squaredExcessRatio atTop (𝓝 2) := by
  unfold squaredExcessRatio
  convert outputExcess_limit.div inputExcess_limit (by norm_num) using 1 <;> norm_num

theorem normExcessRatio_rationalized {L : ℝ} (hL : 0 < L) :
    normExcessRatio L = squaredExcessRatio L *
      (Real.sqrt (1 + inputExcess L / L) + 1) /
      (Real.sqrt (1 + outputExcess L / L) + 1) := by
  have hi := inputExcess_pos L
  have ho := outputExcess_pos L
  have hsi := Real.sq_sqrt (show 0 ≤ 1 + inputExcess L / L by positivity)
  have hso := Real.sq_sqrt (show 0 ≤ 1 + outputExcess L / L by positivity)
  have hni : Real.sqrt (1 + inputExcess L/L)-1 ≠ 0 := by
    have hdiv : 0 < inputExcess L/L := div_pos hi hL
    intro he
    have : Real.sqrt (1 + inputExcess L/L) = 1 := sub_eq_zero.mp he
    rw [this] at hsi
    nlinarith
  have hno : Real.sqrt (1 + outputExcess L/L)+1 ≠ 0 := by positivity
  have hsi' : (Real.sqrt (1 + inputExcess L/L)^2-1)*L = inputExcess L := by
    rw [hsi]
    field_simp
    ring
  have hso' : (Real.sqrt (1 + outputExcess L/L)^2-1)*L = outputExcess L := by
    rw [hso]
    field_simp
    ring
  unfold normExcessRatio squaredExcessRatio
  generalize Real.sqrt (1 + inputExcess L/L) = u at *
  generalize Real.sqrt (1 + outputExcess L/L) = v at *
  change (v-1)/(u-1) = (outputExcess L/inputExcess L)*(u+1)/(v+1)
  field_simp [hni, hno, ne_of_gt hi]
  rw [← hsi', ← hso']
  ring

theorem normExcessRatio_limit : Tendsto normExcessRatio atTop (𝓝 2) := by
  have hi : Tendsto (fun L : ℝ => 1/L) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have hia : Tendsto (fun L : ℝ => 1 + inputExcess L/L) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (inputExcess_limit.mul hi)
  have hoa : Tendsto (fun L : ℝ => 1 + outputExcess L/L) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (outputExcess_limit.mul hi)
  have hs := (squaredExcessRatio_limit.mul
    (hia.sqrt.add_const 1)).div (hoa.sqrt.add_const 1) (by norm_num)
  have heq : normExcessRatio =ᶠ[atTop] (fun L : ℝ => squaredExcessRatio L *
      (Real.sqrt (1 + inputExcess L/L)+1)/(Real.sqrt (1 + outputExcess L/L)+1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    exact normExcessRatio_rationalized hL
  apply Tendsto.congr' heq.symm
  convert hs using 1 <;> norm_num

#print axioms squaredExcessRatio_limit
#print axioms normExcessRatio_limit

end NLA.RA09.Paper
