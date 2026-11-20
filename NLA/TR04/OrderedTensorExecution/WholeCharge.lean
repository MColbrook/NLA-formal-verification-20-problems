module

/- Full charged indexed-array solver polynomial operation bound.
This model currently uses the frozen static tensor layout; the concrete
lexicographic layout bridge is a separate obligation, not a free runtime oracle. -/
public import NLA.TR04.OrderedTensorExecution.RuntimeCounts
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion

@[simp] theorem spectralRun_charge {m n : ℕ} (A : Rect m n) :
    charge (spectralRun A)=(m+n+1)^3 := rfl

theorem dense_fifth_bounds (m : ℕ) (ns : List ℕ) (hm : 1≤m) (hmode : ∀ a∈ns,2≤a) :
    let N := Reference.TensorArithmeticExecution.denseSize m ns
    m≤N ∧ Reference.TensorArithmeticExecution.modeCard ns≤N ∧ 1≤N ∧ N≤N^5 ∧ N^2≤N^5 ∧ N^3≤N^5 := by
  dsimp
  let N := Reference.TensorArithmeticExecution.denseSize m ns
  have hp := Reference.TensorArithmeticExecution.modeCard_pos ns
    (fun a ha => (by omega : 2≤a → 1≤a) (hmode a ha))
  have hmN : m≤N := by dsimp [N,Reference.TensorArithmeticExecution.denseSize]; nlinarith
  have hPN : Reference.TensorArithmeticExecution.modeCard ns≤N := by dsimp [N,Reference.TensorArithmeticExecution.denseSize]; nlinarith
  have hN : 1≤N := hm.trans hmN
  have hn : 0<N := by omega
  have h2 : 1≤N^2 := Nat.succ_le_of_lt (pow_pos hn 2)
  have h3 : 1≤N^3 := Nat.succ_le_of_lt (pow_pos hn 3)
  have h4 : 1≤N^4 := Nat.succ_le_of_lt (pow_pos hn 4)
  have h15 : N≤N^5 := by
    calc _≤N*(N^4) := le_mul_of_one_le_right (Nat.zero_le _) h4
         _=N^5 := by ring
  have h25 : N^2≤N^5 := by
    calc _≤N^2*N^3 := le_mul_of_one_le_right (Nat.zero_le _) h3
         _=N^5 := by ring
  have h35 : N^3≤N^5 := by
    calc _≤N^3*N^2 := le_mul_of_one_le_right (Nat.zero_le _) h2
         _=N^5 := by ring
  exact ⟨hmN,hPN,hN,h15,h25,h35⟩

theorem actual_candidate_generator_dense_charge {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a) :
    charge (candidatesExecutionRun A r rs)≤1470*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^5 := by
  let N := Reference.TensorArithmeticExecution.denseSize m (n::ns)
  have ⟨hmN,hPN,hN,h15,h25,h35⟩ := dense_fifth_bounds m (n::ns) hm hmode
  have hsum : m+Reference.TensorArithmeticExecution.modeCard (n::ns)+1≤3*N := by omega
  have hsq := Nat.mul_le_mul hsum hsum
  have hcube := Nat.mul_le_mul hsq hsum
  have hs : (m+Reference.TensorArithmeticExecution.modeCard (n::ns)+1)^3≤27*N^3 := by
    calc _≤(3*N)^3 := by simpa only [pow_succ,pow_zero,Nat.one_mul] using hcube
         _=27*N^3 := by ring
  have hg := candidateDataRun_charge A (spectralRun (denseTensor A)).value.1
    (spectralRun (denseTensor A)).value.2 r rs hm hmode
  have hp : m*(1421*N^4)≤1421*N^5 := by
    calc _≤N*(1421*N^4) := Nat.mul_le_mul_right _ hmN
         _=1421*N^5 := by ring
  simp only [candidatesExecutionRun,charge_bind,spectralRun_charge]
  change (m+Reference.TensorArithmeticExecution.modeCard (n::ns)+1)^3+charge
    (candidateDataRun A (spectralRun (denseTensor A)).value.1
      (spectralRun (denseTensor A)).value.2 r rs)≤1470*N^5
  change charge (candidateDataRun A (spectralRun (denseTensor A)).value.1
    (spectralRun (denseTensor A)).value.2 r rs)≤9*m+11+m*(1421*N^4) at hg
  nlinarith

theorem actual_full_solver_dense_polynomial_charge {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a) :
    charge (solverExecutionRun A r rs)≤1500*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^5 := by
  let N := Reference.TensorArithmeticExecution.denseSize m (n::ns)
  have ⟨hmN,hPN,hN,h15,h25,h35⟩ := dense_fifth_bounds m (n::ns) hm hmode
  have hg := actual_candidate_generator_dense_charge A r rs hm hmode
  have hcount := actual_candidate_execution_count A r rs hm
  simp only [solverExecutionRun,charge_bind]
  cases hs : (candidatesExecutionRun A r rs).value with
  | nil => simp only [hs,List.length_nil] at hcount; omega
  | cons x xs =>
      simp only [charge_lift,Reference.TensorArithmeticExecution.actual_first_minimum_execution_charge]
      rw [hs] at hcount
      have hlm : xs.length≤m := by simpa using (Nat.le_of_succ_le hcount.2)
      have hl : xs.length≤N := hlm.trans hmN
      have hstep : 2*(m*(5*Reference.TensorArithmeticExecution.modeCard (n::ns)+2)+1)+1≤17*N := by
        dsimp [N,Reference.TensorArithmeticExecution.denseSize] at hmN hN ⊢
        nlinarith
      have hsel := Nat.mul_le_mul hl hstep
      have hsel' : xs.length*(2*(m*(5*Reference.TensorArithmeticExecution.modeCard (n::ns)+2)+1)+1)≤17*N^2 := by
        simpa [pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hsel
      change charge (candidatesExecutionRun A r rs)≤1470*N^5 at hg
      change charge (candidatesExecutionRun A r rs)+
        xs.length*(2*(m*(5*Reference.TensorArithmeticExecution.modeCard (n::ns)+2)+1)+1)≤1500*N^5
      nlinarith

#print axioms actual_candidate_generator_dense_charge
#print axioms actual_full_solver_dense_polynomial_charge
end
end Reference.OrderedTensorExecution
