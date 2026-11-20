module

public import NLA.IV04.ConcreteOracleSearchProof.Composition
public import NLA.IV04.ExactOutputSupport.Recovery

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open Complexity IV04.Paper.Computational IV04.Paper.InequalityCertificate
open Reference.IV04AffinePolyhedronSteps Reference.IV04ExactOutputSupport
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem natural_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr]
  exact IV04.Paper.bits_foldr n

theorem typed_certificate_denominator_bound {n : ℕ} (p : Fin n → ℤ) (d bound : ℕ)
    (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound) :
    d≤2^bound := by
  have hl : d.bits.length≤bound := by
    rw [Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode,pair_length] at hlen
    omega
  calc
    d=wordValue d.bits := (Reference.IV04ConcreteOracleSearchProof.natural_bits_value d).symm
    _≤2^d.bits.length := (word_value_lt_pow_length _).le
    _≤2^bound := Nat.pow_le_pow_right (by omega) hl

theorem capped_threshold_certificate_coordinate_exact {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (p : Fin n → ℤ) (d : ℕ) (hd : 0<d)
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤(p j : ℝ)/(d : ℝ))
    (bound : ℕ) (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound)
    (lower upper : ℚ) (hu : (p j : ℚ)/(d : ℚ)≤upper)
    (hwidth : upper-lower<1/((2^bound : ℕ) : ℚ)^2)
    (certificate : List Bool) (hcertlen : certificate.length≤bound)
    (haccept : Reference.IV04ConcreteOracleSearch.acceptedCertificate
      (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j lower) (Reference.IV04ConcreteOracleSearch.thresholdBounds b lower)) certificate) :
    Reference.IV04ConcreteOracleSearch.certificateCoordinate j.val certificate=(p j : ℚ)/(d : ℚ) := by
  obtain ⟨hfeas,hden⟩ := Reference.IV04ConcreteOracleSearchProof.accepted_certificate_point
    (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j lower) (Reference.IV04ConcreteOracleSearch.thresholdBounds b lower) (by omega) certificate haccept
  obtain ⟨horiginal,hlower⟩ := (Reference.IV04ConcreteOracleSearchProof.threshold_feasible_iff A b j lower _).mp hfeas
  have hupper := hmax _ horiginal
  change (Reference.IV04ConcreteOracleSearch.certificateCoordinate j.val certificate : ℝ)≤(p j : ℝ)/(d : ℝ) at hupper
  change (lower : ℝ)≤(Reference.IV04ConcreteOracleSearch.certificateCoordinate j.val certificate : ℝ) at hlower
  have hqmax : Reference.IV04ConcreteOracleSearch.certificateCoordinate j.val certificate≤(p j : ℚ)/(d : ℚ) := by exact_mod_cast hupper
  have hLq : lower≤Reference.IV04ConcreteOracleSearch.certificateCoordinate j.val certificate := by exact_mod_cast hlower
  have hqU := hqmax.trans hu
  have hLmax := hLq.trans hqmax
  have hqden : (Reference.IV04ConcreteOracleSearch.certificateCoordinate j.val certificate).den≤2^bound :=
    (hden j).trans (Nat.pow_le_pow_right (by omega) hcertlen)
  have hmaxden : ((p j : ℚ)/(d : ℚ)).den≤2^bound :=
    (Reference.IV04ConcreteOracleSearchProof.natural_fraction_den_le _ _ hd).trans (Reference.IV04ConcreteOracleSearchProof.typed_certificate_denominator_bound p d bound hlen)
  exact unique_rational_in_narrow_bracket (by positivity) hqden hmaxden hLq hqU hLmax hu hwidth

theorem coordinateRecovery_query_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (bound fuel : ℕ) (lower upper : ℚ) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost (fuel+bound) (Reference.IV04ConcreteOracleSearch.coordinateRecovery A b j bound fuel lower upper) := by
  apply Reference.IV04ConcreteOracleSearchProof.queriesAtMost_bindProgram fuel bound
  · exact Reference.IV04ConcreteOracleSearchProof.cappedBinarySearch_query_bound _ _ _ _ _ _ _
  · intro bracket
    have h := Reference.IV04ConcreteOracleSearchProof.queriesAtMost_bindProgram bound 0
      (Reference.IV04ConcreteOracleSearch.selfReduce (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j bracket.1) (Reference.IV04ConcreteOracleSearch.thresholdBounds b bracket.1)) bound bound [])
      (fun result => Reference.IV04ConcreteOracleSearch.QueryProgram.done (result.map (Reference.IV04ConcreteOracleSearch.certificateCoordinate j.val)))
      (Reference.IV04ConcreteOracleSearchProof.selfReduce_query_bound _ _ _ _) (fun _ => trivial)
    simpa using h

theorem coordinateRecovery_actual_output_exact {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (p : Fin n → ℤ) (d : ℕ) (hd : 0<d)
    (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) (fun k => (p k : ℝ)/(d : ℝ)))
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤(p j : ℝ)/(d : ℝ))
    (bound : ℕ) (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound)
    (fuel : ℕ) (lower upper : ℚ)
    (hl : (lower : ℝ)≤(p j : ℝ)/(d : ℝ)) (hu : (p j : ℝ)/(d : ℝ)≤(upper : ℝ))
    (hwidth : (upper-lower)/2^fuel<1/((2^bound : ℕ) : ℚ)^2) :
    Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.coordinateRecovery A b j bound fuel lower upper)=some ((p j : ℚ)/(d : ℚ)) := by
  let bracket := Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound fuel lower upper)
  obtain ⟨hlo,hhi,hw⟩ := Reference.IV04ConcreteOracleSearchProof.cappedBinarySearch_actual_optimum_bracket A b j p d hd hx hmax bound hlen
    fuel lower upper hl hu
  have hmember : Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.cappedThresholdQuery A b j bracket.1 bound) :=
    (Reference.IV04ConcreteOracleSearchProof.capped_threshold_membership_iff_actual_optimum A b j p d hd hx hmax bound hlen bracket.1).mpr hlo
  obtain ⟨certificate,he,hclen,ha⟩ := Reference.IV04ConcreteOracleSearchProof.selfReduce_recovers_certificate
    (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j bracket.1) (Reference.IV04ConcreteOracleSearch.thresholdBounds b bracket.1)) bound bound []
    hmember (by simp)
  have hhiQ : (p j : ℚ)/(d : ℚ)≤bracket.2 := by exact_mod_cast hhi
  have hnarrow : bracket.2-bracket.1<1/((2^bound : ℕ) : ℚ)^2 := by
    rw [hw]
    exact hwidth
  have hcoord := Reference.IV04ConcreteOracleSearchProof.capped_threshold_certificate_coordinate_exact A b j p d hd hmax bound hlen
    bracket.1 bracket.2 hhiQ hnarrow certificate hclen ha
  unfold Reference.IV04ConcreteOracleSearch.coordinateRecovery
  rw [Reference.IV04ConcreteOracleSearchProof.execute_bindProgram]
  change Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.bindProgram
    (Reference.IV04ConcreteOracleSearch.selfReduce (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j bracket.1) (Reference.IV04ConcreteOracleSearch.thresholdBounds b bracket.1)) bound bound [])
    (fun result => Reference.IV04ConcreteOracleSearch.QueryProgram.done (result.map (Reference.IV04ConcreteOracleSearch.certificateCoordinate j.val))))=_
  rw [Reference.IV04ConcreteOracleSearchProof.execute_bindProgram,he]
  simp only [Reference.IV04ConcreteOracleSearch.execute,Option.map_some,hcoord]

#print axioms natural_bits_value

#print axioms typed_certificate_denominator_bound

#print axioms capped_threshold_certificate_coordinate_exact

#print axioms coordinateRecovery_query_bound

#print axioms coordinateRecovery_actual_output_exact
end Reference.IV04ConcreteOracleSearchProof
