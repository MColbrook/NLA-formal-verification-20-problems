module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

/-- The repeated eigenvalue of a scalar matrix plus a rank-one matrix is
rationally recoverable from three traces, except on the explicitly identified
nilpotent locus, where the first trace alone recovers it. -/
theorem scalar_rank_one_trace_identities {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ) (α β : ℂ) (htr : R.trace = α) (hsq : R*R = α • R) :
    let n : ℂ := Fintype.card ι
    let K := β • (1 : Matrix ι ι ℂ)+R
    K.trace = n*β+α ∧
      n*(K^2).trace-K.trace^2 = (n-1)*α^2 ∧
      n^2*(K^3).trace-3*n*K.trace*(K^2).trace+2*K.trace^3 =
        (n-1)*(n-2)*α^3 := by
  dsimp only
  let K := β • (1 : Matrix ι ι ℂ)+R
  have h2 : K^2 = β^2 • (1 : Matrix ι ι ℂ)+(2*β+α) • R := by
    simp only [K,pow_two,mul_add,add_mul,Matrix.smul_mul,Matrix.mul_smul,
      one_mul,mul_one,smul_smul,hsq]
    module
  have h3 : K^3 = β^3 • (1 : Matrix ι ι ℂ)+(3*β^2+3*β*α+α^2) • R := by
    rw [pow_succ,h2]
    simp only [K,mul_add,add_mul,Matrix.smul_mul,Matrix.mul_smul,
      one_mul,mul_one,smul_smul,hsq]
    module
  have hT : K.trace = (Fintype.card ι : ℂ)*β+α := by
    simp only [K,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,htr,smul_eq_mul]
    ring
  have hS : (K^2).trace = (Fintype.card ι : ℂ)*β^2+2*β*α+α^2 := by
    rw [h2]
    simp only [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,htr,smul_eq_mul]
    ring
  have hU : (K^3).trace = (Fintype.card ι : ℂ)*β^3+3*β^2*α+3*β*α^2+α^3 := by
    rw [h3]
    simp only [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,htr,smul_eq_mul]
    ring
  refine ⟨hT, ?_, ?_⟩
  · change (Fintype.card ι : ℂ)*(K^2).trace-K.trace^2 = _
    rw [hT,hS]
    ring
  · change (Fintype.card ι : ℂ)^2*(K^3).trace-
      3*(Fintype.card ι : ℂ)*K.trace*(K^2).trace+2*K.trace^3 = _
    rw [hT,hS,hU]
    ring

theorem scalar_rank_one_rational_recovery {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ) (α β : ℂ) (htr : R.trace = α) (hsq : R*R = α • R)
    (hn : 3 ≤ Fintype.card ι) (hα : α ≠ 0) :
    let n : ℂ := Fintype.card ι
    let K := β • (1 : Matrix ι ι ℂ)+R
    let V := n*(K^2).trace-K.trace^2
    let W := n^2*(K^3).trace-3*n*K.trace*(K^2).trace+2*K.trace^3
    V ≠ 0 ∧ (K.trace-W/((n-2)*V))/n = β := by
  dsimp only
  obtain ⟨hT,hV,hW⟩ := scalar_rank_one_trace_identities R α β htr hsq
  rw [hW,hV,hT]
  have hn0 : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (Fintype.card ι : ℂ)-1 ≠ 0 := by
    have h : Fintype.card ι ≠ 1 := by omega
    exact sub_ne_zero.mpr (by exact_mod_cast h)
  have hn2 : (Fintype.card ι : ℂ)-2 ≠ 0 := by
    have h : Fintype.card ι ≠ 2 := by omega
    exact sub_ne_zero.mpr (by exact_mod_cast h)
  refine ⟨mul_ne_zero hn1 (pow_ne_zero _ hα), ?_⟩
  field_simp [hn0,hn1,hn2,hα]
  <;> ring

theorem scalar_rank_one_nilpotent_recovery {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℂ) (β : ℂ) (htr : R.trace = 0) (hn : 0 < Fintype.card ι) :
    (β • (1 : Matrix ι ι ℂ)+R).trace/(Fintype.card ι : ℂ) = β := by
  simp only [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,htr,smul_eq_mul,add_zero]
  have hn0 : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact mul_div_cancel_right₀ β hn0

#print axioms scalar_rank_one_trace_identities
#print axioms scalar_rank_one_rational_recovery
#print axioms scalar_rank_one_nilpotent_recovery
end NLA.TR27.Paper
