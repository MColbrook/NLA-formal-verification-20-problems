module

public import NLA.IV04.ConcreteOracleSearchProof.CappedBinarySearch

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof

open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem execute_bindProgram {α β : Type} (program : Reference.IV04ConcreteOracleSearch.QueryProgram α) (f : α → Reference.IV04ConcreteOracleSearch.QueryProgram β) :
    Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.bindProgram program f)=Reference.IV04ConcreteOracleSearch.execute (f (Reference.IV04ConcreteOracleSearch.execute program)) := by
  induction program with
  | done a => rfl
  | ask q next ih =>
    classical
    exact ih (decide (Reference.IV04ConcreteOracleSearch.prefixMembership q))

theorem queriesAtMost_mono {α : Type} (lower upper : ℕ) (program : Reference.IV04ConcreteOracleSearch.QueryProgram α)
    (hle : lower≤upper) (h : Reference.IV04ConcreteOracleSearch.queriesAtMost lower program) : Reference.IV04ConcreteOracleSearch.queriesAtMost upper program := by
  induction lower generalizing upper program with
  | zero => cases program with
    | done a => simp [Reference.IV04ConcreteOracleSearch.queriesAtMost]
    | ask q next => contradiction
  | succ lower ih =>
    cases program with
    | done a => simp [Reference.IV04ConcreteOracleSearch.queriesAtMost]
    | ask q next =>
      cases upper with
      | zero => omega
      | succ upper =>
        intro answer
        exact ih upper (next answer) (by omega) (h answer)

theorem queriesAtMost_bindProgram {α β : Type} (first second : ℕ)
    (program : Reference.IV04ConcreteOracleSearch.QueryProgram α) (f : α → Reference.IV04ConcreteOracleSearch.QueryProgram β)
    (hp : Reference.IV04ConcreteOracleSearch.queriesAtMost first program) (hf : ∀ a, Reference.IV04ConcreteOracleSearch.queriesAtMost second (f a)) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost (first+second) (Reference.IV04ConcreteOracleSearch.bindProgram program f) := by
  induction first generalizing program with
  | zero => cases program with
    | done a => simpa only [Reference.IV04ConcreteOracleSearch.bindProgram,Nat.zero_add] using hf a
    | ask q next => contradiction
  | succ first ih =>
    cases program with
    | done a => exact Reference.IV04ConcreteOracleSearchProof.queriesAtMost_mono second (first+1+second) (f a) (by omega) (hf a)
    | ask q next =>
      have he : first+1+second=(first+second)+1 := by omega
      rw [he]
      intro answer
      exact ih (next answer) (hp answer)

theorem executeCounting_result {α : Type} (program : Reference.IV04ConcreteOracleSearch.QueryProgram α) :
    (Reference.IV04ConcreteOracleSearch.executeCounting program).1=Reference.IV04ConcreteOracleSearch.execute program := by
  induction program with
  | done a => rfl
  | ask q next ih =>
    classical
    exact ih (decide (Reference.IV04ConcreteOracleSearch.prefixMembership q))

theorem executeCounting_bound {α : Type} (bound : ℕ) (program : Reference.IV04ConcreteOracleSearch.QueryProgram α)
    (h : Reference.IV04ConcreteOracleSearch.queriesAtMost bound program) : (Reference.IV04ConcreteOracleSearch.executeCounting program).2≤bound := by
  classical
  induction bound generalizing program with
  | zero => cases program with
    | done a => simp [Reference.IV04ConcreteOracleSearch.executeCounting]
    | ask q next => contradiction
  | succ bound ih =>
    cases program with
    | done a => simp [Reference.IV04ConcreteOracleSearch.executeCounting]
    | ask q next =>
      have hc := ih (next (decide (Reference.IV04ConcreteOracleSearch.prefixMembership q))) (h _)
      exact Nat.succ_le_succ hc

#print axioms execute_bindProgram

#print axioms queriesAtMost_mono

#print axioms queriesAtMost_bindProgram

#print axioms executeCounting_result

#print axioms executeCounting_bound
end Reference.IV04ConcreteOracleSearchProof
