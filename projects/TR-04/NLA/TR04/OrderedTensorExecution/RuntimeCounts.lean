module

/- Actual generated candidate nonemptiness and completion count, before selection. -/
public import NLA.TR04.OrderedTensorExecution.ProgramLoops
public import NLA.TR04.OrderedTensorExecution.GeneratorCharge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion

theorem candidateDataRun_count {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (sigma : Fin m → ℝ) (r : ℕ) (rs : List ℕ)
    (hm : 1≤m) :
    0<(candidateDataRun A V sigma r rs).value.length ∧
    (candidateDataRun A V sigma r rs).value.length≤m := by
  let positive := (aboveScanRun sigma 0).value
  let tau := (sigmaAtRun sigma (r-1)).value
  let above := (aboveScanRun sigma tau).value
  let boundary := (equalScanRun sigma tau).value
  let s := r-above.length
  have hb : boundary.length≤m := (scan_length_le sigma tau).2
  by_cases hg : r<positive.length
  · by_cases hn : 0<boundary.length
    · by_cases hf : s=boundary.length
      · dsimp only [positive,tau,above,boundary,s] at hg hn hf
        simp [candidateDataRun,hg,hn,hf]; omega
      · dsimp only [positive,tau,above,boundary,s] at hg hn hf hb
        simpa [candidateDataRun,hg,hn,hf] using And.intro hn hb
    · dsimp only [positive,tau,above,boundary,s] at hg hn
      simp [candidateDataRun,hg,hn]; omega
  · dsimp only [positive] at hg
    simp [candidateDataRun,hg]; omega

theorem actual_candidate_execution_count {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 1≤m) :
    0<(candidatesExecutionRun A r rs).value.length ∧
    (candidatesExecutionRun A r rs).value.length≤m := by
  exact candidateDataRun_count A _ _ r rs hm

#print axioms candidateDataRun_count
#print axioms actual_candidate_execution_count
end
end Reference.OrderedTensorExecution
