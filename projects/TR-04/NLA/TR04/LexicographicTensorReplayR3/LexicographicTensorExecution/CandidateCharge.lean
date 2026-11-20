module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Charges derived from actual copied candidate frames and actual TT execution. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.CandidateDefinitions
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.FrameCopies
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorArithmetic.PolynomialCharge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion

theorem actual_cyclic_execution_charge {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (sigma : Fin m → ℝ)
    (tau : ℝ) (s j : ℕ) (rs : List ℕ) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a) :
    charge (cyclicExecutionRun A V sigma tau s j rs) ≤
      4*m*m+13*m+1404*(Reference.LexTensorArithmeticExecution.denseSize m (n::ns))^4 := by
  let boundary := (equalScanRun sigma tau).value
  let indices := (windowScanRun sigma tau boundary s j).value
  have hb : boundary.length ≤ m := by
    dsimp [boundary]
    rw [equalScanRun_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have hi : indices.length ≤ m := by
    dsimp [indices]
    rw [windowScanRun,filterRun_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have he := equalScanRun_charge sigma tau
  have hw := windowScanRun_charge sigma tau boundary s j
  have hf := frameFromListRun_charge V indices
  have hc := Reference.LexTensorArithmeticExecution.actual_completeFrame_dense_polynomial_charge
    A (frameFromListRun V indices).value rs hm hi hmode
  simp only [cyclicExecutionRun,charge_bind,charge_lift]
  change charge (equalScanRun sigma tau)+
    (charge (windowScanRun sigma tau boundary s j)+
      (charge (frameFromListRun V indices)+
        Reference.LexTensorArithmeticExecution.charge
          (Reference.LexTensorArithmeticExecution.completionRun A (frameFromListRun V indices).value rs)))≤_
  nlinarith

theorem actual_cyclic_execution_dense_polynomial_charge {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (sigma : Fin m → ℝ)
    (tau : ℝ) (s j : ℕ) (rs : List ℕ) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a) :
    charge (cyclicExecutionRun A V sigma tau s j rs) ≤
      1421*(Reference.LexTensorArithmeticExecution.denseSize m (n::ns))^4 := by
  let N := Reference.LexTensorArithmeticExecution.denseSize m (n::ns)
  have hp := Reference.LexTensorArithmeticExecution.modeCard_pos (n::ns)
    (fun a ha => (by omega : 2≤a → 1≤a) (hmode a ha))
  have hmN : m≤N := by dsimp [N,Reference.LexTensorArithmeticExecution.denseSize]; nlinarith
  have hN : 1≤N := hm.trans hmN
  have hN2 : N≤N*N := by nlinarith
  have hN4 : N*N≤(N*N)*(N*N) := Nat.mul_le_mul hN2 hN2
  have hp4 : (N*N)*(N*N)=N^4 := by ring
  have hm2 : m*m≤N*N := Nat.mul_le_mul hmN hmN
  have hc := actual_cyclic_execution_charge A V sigma tau s j rs hm hmode
  change charge (cyclicExecutionRun A V sigma tau s j rs)≤1421*N^4
  change charge (cyclicExecutionRun A V sigma tau s j rs)≤4*m*m+13*m+1404*N^4 at hc
  nlinarith

#print axioms actual_cyclic_execution_charge
#print axioms actual_cyclic_execution_dense_polynomial_charge
end
end Reference.LexTensorExecution
