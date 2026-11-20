module

public import NLA.IV04.ConcreteOracleSearchProof.NPBridge

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open Complexity IV04.Paper.Computational IV04.Paper.InequalityCertificate
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem typed_certificate_numerator_bound {n : ℕ} (p : Fin n → ℤ) (d bound : ℕ)
    (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound) :
    ∀ j, |p j|≤((2^bound : ℕ) : ℤ) := by
  intro j
  have hmem : Reference.IV04ConcreteOracleSearch.inequalityIntegerWord (p j) ∈ (Reference.IV04ConcreteOracleSearch.integerVectorList p).map Reference.IV04ConcreteOracleSearch.inequalityIntegerWord := by
    exact List.mem_map.mpr ⟨p j,List.mem_ofFn.mpr ⟨j,rfl⟩,rfl⟩
  have hw := payload_member_length_le _ _ hmem
  rw [Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode,pair_length] at hlen
  have hl : (Reference.IV04ConcreteOracleSearch.inequalityIntegerWord (p j)).length≤bound := by omega
  exact (integer_word_magnitude_le_pow_length (p j)).trans (by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2 : ℕ)) hl)

theorem typed_certificate_initial_bracket {n : ℕ} (p : Fin n → ℤ) (d bound : ℕ)
    (hd : 0<d) (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound)
    (j : Fin n) :
    ((-((2 : ℚ)^bound) : ℚ) : ℝ)≤(p j : ℝ)/(d : ℝ) ∧
      (p j : ℝ)/(d : ℝ)≤((2 : ℚ)^bound : ℝ) := by
  have hp : |(p j : ℝ)|≤(2 : ℝ)^bound := by
    exact_mod_cast Reference.IV04ConcreteOracleSearchProof.typed_certificate_numerator_bound p d bound hlen j
  have hdR : (0 : ℝ)<(d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ)≤(d : ℝ) := by exact_mod_cast hd
  have hv : |(p j : ℝ)/(d : ℝ)|≤(2 : ℝ)^bound := by
    rw [abs_div,abs_of_pos hdR]
    apply (div_le_iff₀ hdR).mpr
    have hn : (0 : ℝ)≤(2 : ℝ)^bound := by positivity
    nlinarith
  simpa using abs_le.mp hv

theorem automatic_width_strict (bound : ℕ) :
    ((2 : ℚ)^bound-(-((2 : ℚ)^bound)))/2^(3*bound+2)<
      1/((2^bound : ℕ) : ℚ)^2 := by
  have hpow : (2 : ℚ)^(3*bound+2)=4*((2 : ℚ)^bound)^3 := by
    calc
      _=((2 : ℚ)^bound)^3*(2 : ℚ)^2 := by
        rw [← pow_mul,← pow_add]
        congr 1
        omega
      _=_ := by ring
  have hcast : ((2^bound : ℕ) : ℚ)=(2 : ℚ)^bound := by norm_cast
  rw [hcast,hpow]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have ht : (0 : ℚ)<((2 : ℚ)^bound)^3 := by positivity
  nlinarith

theorem boundedCoordinateRecovery_actual_query_count {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n) (bound : ℕ) :
    (Reference.IV04ConcreteOracleSearch.executeCounting (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)).2≤4*bound+2 := by
  apply Reference.IV04ConcreteOracleSearchProof.executeCounting_bound
  have he : 4*bound+2=(3*bound+2)+bound := by omega
  rw [he]
  exact Reference.IV04ConcreteOracleSearchProof.coordinateRecovery_query_bound _ _ _ _ _ _ _

theorem boundedCoordinateRecovery_actual_output_exact {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (p : Fin n → ℤ) (d : ℕ) (hd : 0<d)
    (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) (fun k => (p k : ℝ)/(d : ℝ)))
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤(p j : ℝ)/(d : ℝ))
    (bound : ℕ) (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound) :
    Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)=some ((p j : ℚ)/(d : ℚ)) := by
  obtain ⟨hl,hu⟩ := Reference.IV04ConcreteOracleSearchProof.typed_certificate_initial_bracket p d bound hd hlen j
  apply Reference.IV04ConcreteOracleSearchProof.coordinateRecovery_actual_output_exact A b j p d hd hx hmax bound hlen
    (3*bound+2) (-((2 : ℚ)^bound)) ((2 : ℚ)^bound)
  · simpa using hl
  · simpa using hu
  · exact Reference.IV04ConcreteOracleSearchProof.automatic_width_strict bound

#print axioms typed_certificate_numerator_bound

#print axioms typed_certificate_initial_bracket

#print axioms automatic_width_strict

#print axioms boundedCoordinateRecovery_actual_query_count

#print axioms boundedCoordinateRecovery_actual_output_exact
end Reference.IV04ConcreteOracleSearchProof
