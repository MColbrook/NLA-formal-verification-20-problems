module

/- Actual prefix completion polynomial charge, with no supplied runtime bound. -/
public import NLA.TR04.OrderedTensorExecution.ProgramLoops
public import NLA.TR04.TensorArithmeticExecution.PolynomialCharge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion

theorem actual_prefix_completion_dense_charge {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (k : ℕ) (rs : List ℕ)
    (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a) :
    charge (prefixCompletionRun A V k rs) ≤
      1405*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^4 := by
  let N := Reference.TensorArithmeticExecution.denseSize m (n::ns)
  have hp := Reference.TensorArithmeticExecution.modeCard_pos (n::ns)
    (fun a ha => (by omega : 2≤a → 1≤a) (hmode a ha))
  have hmN : m≤N := by dsimp [N,Reference.TensorArithmeticExecution.denseSize]; nlinarith
  have hN : 1≤N := hm.trans hmN
  have hN2 : N≤N*N := by nlinarith
  have hN4 : N*N≤(N*N)*(N*N) := Nat.mul_le_mul hN2 hN2
  have hp4 : (N*N)*(N*N)=N^4 := by ring
  have hm2 : m*m≤N*N := Nat.mul_le_mul hmN hmN
  have hk : min k m≤m := Nat.min_le_right k m
  have hc := Reference.TensorArithmeticExecution.actual_completeFrame_dense_polynomial_charge
    A (prefixFrameRun V k).value rs hm hk hmode
  simp only [prefixCompletionRun,charge_bind,charge_lift,prefixFrameRun_charge]
  change m*min k m+Reference.TensorArithmeticExecution.charge
    (Reference.TensorArithmeticExecution.completionRun A (prefixFrameRun V k).value rs)≤1405*N^4
  change Reference.TensorArithmeticExecution.charge
    (Reference.TensorArithmeticExecution.completionRun A (prefixFrameRun V k).value rs)≤1404*N^4 at hc
  nlinarith

#print axioms actual_prefix_completion_dense_charge
end
end Reference.OrderedTensorExecution
