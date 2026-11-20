module

public import NLA.IV04.ConcreteOracleSearchProof.Threshold

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem binarySearch_query_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (fuel : ℕ) (lower upper : ℚ) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost fuel (Reference.IV04ConcreteOracleSearch.binarySearch A b j fuel lower upper) := by
  induction fuel generalizing lower upper with
  | zero => trivial
  | succ fuel ih =>
    intro answer
    cases answer <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> apply ih

theorem binarySearch_actual_optimum_bracket {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (x : Fin n → ℝ) (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤x j)
    (fuel : ℕ) (lower upper : ℚ) (hl : (lower : ℝ)≤x j) (hu : x j≤(upper : ℝ)) :
    let result := Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.binarySearch A b j fuel lower upper)
    (result.1 : ℝ)≤x j ∧ x j≤(result.2 : ℝ) ∧
      result.2-result.1=(upper-lower)/2^fuel := by
  classical
  induction fuel generalizing lower upper with
  | zero => exact ⟨hl,hu,by simp [Reference.IV04ConcreteOracleSearch.binarySearch,Reference.IV04ConcreteOracleSearch.execute]⟩
  | succ fuel ih =>
    let midpoint := (lower+upper)/2
    by_cases hm : Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.thresholdQuery A b j midpoint)
    · have hmval : (midpoint : ℝ)≤x j :=
        (Reference.IV04ConcreteOracleSearchProof.threshold_membership_iff_le_actual_optimum A b j x hx hmax midpoint).mp hm
      obtain ⟨hlo,hhi,hw⟩ := ih midpoint upper hmval hu
      have he : Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.binarySearch A b j (fuel+1) lower upper)=
          Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.binarySearch A b j fuel midpoint upper) := by
        simp [Reference.IV04ConcreteOracleSearch.binarySearch,Reference.IV04ConcreteOracleSearch.execute,midpoint,hm]
      rw [he]
      refine ⟨hlo,hhi,hw.trans ?_⟩
      dsimp [midpoint]
      rw [pow_succ]
      field_simp
      ring
    · have hmval : x j≤(midpoint : ℝ) := by
        have hn : ¬(midpoint : ℝ)≤x j :=
          fun h => hm ((Reference.IV04ConcreteOracleSearchProof.threshold_membership_iff_le_actual_optimum A b j x hx hmax midpoint).mpr h)
        exact (lt_of_not_ge hn).le
      obtain ⟨hlo,hhi,hw⟩ := ih lower midpoint hl hmval
      have he : Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.binarySearch A b j (fuel+1) lower upper)=
          Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.binarySearch A b j fuel lower midpoint) := by
        simp [Reference.IV04ConcreteOracleSearch.binarySearch,Reference.IV04ConcreteOracleSearch.execute,midpoint,hm]
      rw [he]
      refine ⟨hlo,hhi,hw.trans ?_⟩
      dsimp [midpoint]
      rw [pow_succ]
      field_simp
      ring

#print axioms binarySearch_query_bound

#print axioms binarySearch_actual_optimum_bracket
end Reference.IV04ConcreteOracleSearchProof
