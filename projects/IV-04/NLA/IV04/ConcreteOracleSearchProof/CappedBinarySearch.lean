module

public import NLA.IV04.ConcreteOracleSearchProof.CappedThreshold

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open IV04.Paper.Computational IV04.Paper.InequalityCertificate Reference.IV04AffinePolyhedronSteps
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem cappedBinarySearch_query_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (bound fuel : ℕ) (lower upper : ℚ) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost fuel (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound fuel lower upper) := by
  induction fuel generalizing lower upper with
  | zero => trivial
  | succ fuel ih =>
    intro answer
    cases answer <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> apply ih

theorem cappedBinarySearch_actual_optimum_bracket {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (p : Fin n → ℤ) (d : ℕ) (hd : 0<d)
    (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) (fun k => (p k : ℝ)/(d : ℝ)))
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤(p j : ℝ)/(d : ℝ))
    (bound : ℕ) (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound)
    (fuel : ℕ) (lower upper : ℚ)
    (hl : (lower : ℝ)≤(p j : ℝ)/(d : ℝ)) (hu : (p j : ℝ)/(d : ℝ)≤(upper : ℝ)) :
    let result := Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound fuel lower upper)
    (result.1 : ℝ)≤(p j : ℝ)/(d : ℝ) ∧ (p j : ℝ)/(d : ℝ)≤(result.2 : ℝ) ∧
      result.2-result.1=(upper-lower)/2^fuel := by
  classical
  induction fuel generalizing lower upper with
  | zero => exact ⟨hl,hu,by simp [Reference.IV04ConcreteOracleSearch.cappedBinarySearch,Reference.IV04ConcreteOracleSearch.execute]⟩
  | succ fuel ih =>
    let midpoint := (lower+upper)/2
    by_cases hm : Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.cappedThresholdQuery A b j midpoint bound)
    · have hmval : (midpoint : ℝ)≤(p j : ℝ)/(d : ℝ) :=
        (Reference.IV04ConcreteOracleSearchProof.capped_threshold_membership_iff_actual_optimum A b j p d hd hx hmax bound hlen midpoint).mp hm
      obtain ⟨hlo,hhi,hw⟩ := ih midpoint upper hmval hu
      have he : Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound (fuel+1) lower upper)=
          Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound fuel midpoint upper) := by
        simp [Reference.IV04ConcreteOracleSearch.cappedBinarySearch,Reference.IV04ConcreteOracleSearch.execute,midpoint,hm]
      rw [he]
      refine ⟨hlo,hhi,hw.trans ?_⟩
      dsimp [midpoint]
      rw [pow_succ]
      field_simp
      ring
    · have hmval : (p j : ℝ)/(d : ℝ)≤(midpoint : ℝ) := by
        have hn : ¬(midpoint : ℝ)≤(p j : ℝ)/(d : ℝ) := fun h =>
          hm ((Reference.IV04ConcreteOracleSearchProof.capped_threshold_membership_iff_actual_optimum A b j p d hd hx hmax bound hlen midpoint).mpr h)
        exact (lt_of_not_ge hn).le
      obtain ⟨hlo,hhi,hw⟩ := ih lower midpoint hl hmval
      have he : Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound (fuel+1) lower upper)=
          Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound fuel lower midpoint) := by
        simp [Reference.IV04ConcreteOracleSearch.cappedBinarySearch,Reference.IV04ConcreteOracleSearch.execute,midpoint,hm]
      rw [he]
      refine ⟨hlo,hhi,hw.trans ?_⟩
      dsimp [midpoint]
      rw [pow_succ]
      field_simp
      ring

#print axioms cappedBinarySearch_query_bound

#print axioms cappedBinarySearch_actual_optimum_bracket
end Reference.IV04ConcreteOracleSearchProof
