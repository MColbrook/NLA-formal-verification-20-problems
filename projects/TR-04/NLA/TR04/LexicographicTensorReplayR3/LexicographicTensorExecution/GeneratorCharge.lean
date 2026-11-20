module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- The full candidate generator has a uniform cost derived from its own branches. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.ProgramLoops
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.CandidateCharge
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.PrefixCharge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion

theorem scan_length_le {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) :
    (aboveScanRun sigma tau).value.length≤m ∧ (equalScanRun sigma tau).value.length≤m := by
  constructor
  · rw [aboveScanRun_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  · rw [equalScanRun_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange

theorem candidateDataRun_charge {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (sigma : Fin m → ℝ) (r : ℕ) (rs : List ℕ)
    (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a) :
    charge (candidateDataRun A V sigma r rs) ≤
      9*m+11+m*(1421*(Reference.LexTensorArithmeticExecution.denseSize m (n::ns))^4) := by
  let N := Reference.LexTensorArithmeticExecution.denseSize m (n::ns)
  let positive := (aboveScanRun sigma 0).value
  let tau := (sigmaAtRun sigma (r-1)).value
  let above := (aboveScanRun sigma tau).value
  let boundary := (equalScanRun sigma tau).value
  let s := r-above.length
  have hp := aboveScanRun_charge sigma 0
  have ha := aboveScanRun_charge sigma tau
  have he := equalScanRun_charge sigma tau
  have hb : boundary.length≤m := (scan_length_le sigma tau).2
  have hc (j : ℕ) := actual_cyclic_execution_dense_polynomial_charge A V sigma tau s j rs hm hmode
  have hpre (k : ℕ) := actual_prefix_completion_dense_charge A V k rs hm hmode
  have hc0 := hc 0
  have hmap := listMapRun_charge
    (fun j : Fin boundary.length => cyclicExecutionRun A V sigma tau s j.val rs)
    (List.finRange boundary.length) (1421*N^4) (by intro j hj; exact hc j.val)
  simp only [List.length_finRange] at hmap
  by_cases hg : r<positive.length
  · by_cases hn : 0<boundary.length
    · by_cases hf : s=boundary.length
      · dsimp only [positive,tau,above,boundary,s] at hg hn hf
        have hc' := actual_cyclic_execution_dense_polynomial_charge A V sigma tau boundary.length 0 rs hm hmode
        simp [candidateDataRun,hg,hn,hf,sigmaAtRun_charge]
        change charge (cyclicExecutionRun A V sigma tau boundary.length 0 rs)≤1421*N^4 at hc'
        change _≤9*m+11+m*(1421*N^4)
        nlinarith
      · dsimp only [positive,tau,above,boundary,s] at hg hn hf
        simp [candidateDataRun,hg,hn,hf,sigmaAtRun_charge]
        change _≤9*m+11+m*(1421*N^4)
        change charge (listMapRun (fun j : Fin boundary.length => cyclicExecutionRun A V sigma tau s j.val rs)
          (List.finRange boundary.length))≤boundary.length*(1421*N^4) at hmap
        nlinarith
    · dsimp only [positive,tau,above,boundary,s] at hg hn
      have hpre' := hpre r
      simp [candidateDataRun,hg,hn,sigmaAtRun_charge]
      change charge (prefixCompletionRun A V r rs)≤1405*N^4 at hpre'
      change _≤9*m+11+m*(1421*N^4)
      nlinarith
  · dsimp only [positive,tau,above,boundary,s] at hg
    have hpre' := hpre positive.length
    simp [candidateDataRun,hg]
    change charge (prefixCompletionRun A V positive.length rs)≤1405*N^4 at hpre'
    change _≤9*m+11+m*(1421*N^4)
    nlinarith

#print axioms candidateDataRun_charge
end
end Reference.LexTensorExecution
