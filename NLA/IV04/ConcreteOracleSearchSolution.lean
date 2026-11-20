module

public import NLA.IV04.ConcreteOracleSearchProof.ActualNPExecution

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearch
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
theorem prefix_length_le_of_membership (instanceCode : List Bool) (bound : ℕ)
    (stem : List Bool) (h : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem⟩) :
    stem.length≤bound := by
  exact Reference.IV04ConcreteOracleSearchProof.prefix_length_le_of_membership instanceCode bound stem h

theorem prefix_membership_child (instanceCode : List Bool) (bound : ℕ)
    (stem : List Bool)
    (h : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem⟩)
    (hnot : ¬Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode stem) :
    Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem++[false]⟩ ∨
    Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem++[true]⟩ := by
  exact Reference.IV04ConcreteOracleSearchProof.prefix_membership_child instanceCode bound stem h hnot

theorem prefix_membership_at_bound (instanceCode : List Bool) (bound : ℕ)
    (stem : List Bool)
    (h : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem⟩) (hbound : bound≤stem.length) :
    Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode stem := by
  exact Reference.IV04ConcreteOracleSearchProof.prefix_membership_at_bound instanceCode bound stem h hbound

theorem selfReduce_query_bound (instanceCode : List Bool) (bound fuel : ℕ)
    (stem : List Bool) : Reference.IV04ConcreteOracleSearch.queriesAtMost fuel (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound fuel stem) := by
  exact Reference.IV04ConcreteOracleSearchProof.selfReduce_query_bound instanceCode bound fuel stem

theorem selfReduce_recovers_certificate (instanceCode : List Bool) (bound fuel : ℕ)
    (stem : List Bool)
    (h : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem⟩)
    (hspace : bound≤stem.length+fuel) :
    ∃ certificate, Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound fuel stem)=some certificate ∧
      certificate.length≤bound ∧ Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate := by
  exact Reference.IV04ConcreteOracleSearchProof.selfReduce_recovers_certificate instanceCode bound fuel stem h hspace

theorem bounded_certificate_self_reduction (instanceCode : List Bool) (bound : ℕ)
    (h : ∃ certificate : List Bool, certificate.length≤bound ∧
      Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost bound (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound bound []) ∧
    ∃ certificate, Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound bound [])=some certificate ∧
      certificate.length≤bound ∧ Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate := by
  exact Reference.IV04ConcreteOracleSearchProof.bounded_certificate_self_reduction instanceCode bound h

theorem actual_feasibility_certificate_search {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m)
    (hne : ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x) :
    let instanceCode := Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b
    let bound := Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial instanceCode.length
    Reference.IV04ConcreteOracleSearch.queriesAtMost bound (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound bound []) ∧
    ∃ certificate, Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound bound [])=some certificate ∧
      certificate.length≤bound ∧ Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate := by
  exact Reference.IV04ConcreteOracleSearchProof.actual_feasibility_certificate_search A b hm hne

theorem threshold_feasible_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (j : Fin n) (r : ℚ) (x : Fin n → ℝ) :
    feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r)) (Reference.IV04ConcreteOracleSearch.integerRealVector (Reference.IV04ConcreteOracleSearch.thresholdBounds b r)) x ↔
      feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x ∧ (r : ℝ)≤x j := by
  exact Reference.IV04ConcreteOracleSearchProof.threshold_feasible_iff A b j r x

theorem threshold_query_membership_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n) (r : ℚ) :
    Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.thresholdQuery A b j r) ↔
      ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x ∧ (r : ℝ)≤x j := by
  exact Reference.IV04ConcreteOracleSearchProof.threshold_query_membership_iff A b j r

theorem threshold_membership_iff_le_actual_optimum {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (x : Fin n → ℝ) (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤x j)
    (r : ℚ) : Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.thresholdQuery A b j r) ↔ (r : ℝ)≤x j := by
  exact Reference.IV04ConcreteOracleSearchProof.threshold_membership_iff_le_actual_optimum A b j x hx hmax r

theorem binarySearch_query_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (fuel : ℕ) (lower upper : ℚ) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost fuel (Reference.IV04ConcreteOracleSearch.binarySearch A b j fuel lower upper) := by
  exact Reference.IV04ConcreteOracleSearchProof.binarySearch_query_bound A b j fuel lower upper

theorem binarySearch_actual_optimum_bracket {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (x : Fin n → ℝ) (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤x j)
    (fuel : ℕ) (lower upper : ℚ) (hl : (lower : ℝ)≤x j) (hu : x j≤(upper : ℝ)) :
    let result := Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.binarySearch A b j fuel lower upper)
    (result.1 : ℝ)≤x j ∧ x j≤(result.2 : ℝ) ∧
      result.2-result.1=(upper-lower)/2^fuel := by
  exact Reference.IV04ConcreteOracleSearchProof.binarySearch_actual_optimum_bracket A b j x hx hmax fuel lower upper hl hu

theorem payloadNth_code (words : List (List Bool)) (j : Fin words.length) :
    Reference.IV04ConcreteOracleSearch.payloadNth j.val (payloadListCode words)=words.get j := by
  exact Reference.IV04ConcreteOracleSearchProof.payloadNth_code words j

theorem natural_fraction_den_le (p : ℤ) (d : ℕ) (hd : 0<d) :
    ((p : ℚ)/(d : ℚ)).den≤d := by
  exact Reference.IV04ConcreteOracleSearchProof.natural_fraction_den_le p d hd

theorem accepted_certificate_point {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m)
    (certificate : List Bool) (haccept : Reference.IV04ConcreteOracleSearch.acceptedCertificate (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b) certificate) :
    feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)
      (Reference.IV04ConcreteOracleSearch.realVector (Reference.IV04ConcreteOracleSearch.certificatePoint n certificate)) ∧
      ∀ j, (Reference.IV04ConcreteOracleSearch.certificatePoint n certificate j).den≤2^certificate.length := by
  exact Reference.IV04ConcreteOracleSearchProof.accepted_certificate_point A b hm certificate haccept

theorem capped_threshold_membership_iff_actual_optimum {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (p : Fin n → ℤ) (d : ℕ) (hd : 0<d)
    (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) (fun k => (p k : ℝ)/(d : ℝ)))
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤(p j : ℝ)/(d : ℝ))
    (bound : ℕ)
    (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound)
    (r : ℚ) : Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.cappedThresholdQuery A b j r bound) ↔
      (r : ℝ)≤(p j : ℝ)/(d : ℝ) := by
  exact Reference.IV04ConcreteOracleSearchProof.capped_threshold_membership_iff_actual_optimum A b j p d hd hx hmax bound hlen r

theorem original_instance_length_le_threshold {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n) (r : ℚ) :
    (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length≤
      (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r) (Reference.IV04ConcreteOracleSearch.thresholdBounds b r)).length := by
  exact Reference.IV04ConcreteOracleSearchProof.original_instance_length_le_threshold A b j r

theorem cappedBinarySearch_query_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (bound fuel : ℕ) (lower upper : ℚ) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost fuel (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound fuel lower upper) := by
  exact Reference.IV04ConcreteOracleSearchProof.cappedBinarySearch_query_bound A b j bound fuel lower upper

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
  exact Reference.IV04ConcreteOracleSearchProof.cappedBinarySearch_actual_optimum_bracket A b j p d hd hx hmax bound hlen fuel lower upper hl hu

theorem execute_bindProgram {α β : Type} (program : Reference.IV04ConcreteOracleSearch.QueryProgram α) (f : α → Reference.IV04ConcreteOracleSearch.QueryProgram β) :
    Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.bindProgram program f)=Reference.IV04ConcreteOracleSearch.execute (f (Reference.IV04ConcreteOracleSearch.execute program)) := by
  exact Reference.IV04ConcreteOracleSearchProof.execute_bindProgram program f

theorem queriesAtMost_mono {α : Type} (lower upper : ℕ) (program : Reference.IV04ConcreteOracleSearch.QueryProgram α)
    (hle : lower≤upper) (h : Reference.IV04ConcreteOracleSearch.queriesAtMost lower program) : Reference.IV04ConcreteOracleSearch.queriesAtMost upper program := by
  exact Reference.IV04ConcreteOracleSearchProof.queriesAtMost_mono lower upper program hle h

theorem queriesAtMost_bindProgram {α β : Type} (first second : ℕ)
    (program : Reference.IV04ConcreteOracleSearch.QueryProgram α) (f : α → Reference.IV04ConcreteOracleSearch.QueryProgram β)
    (hp : Reference.IV04ConcreteOracleSearch.queriesAtMost first program) (hf : ∀ a, Reference.IV04ConcreteOracleSearch.queriesAtMost second (f a)) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost (first+second) (Reference.IV04ConcreteOracleSearch.bindProgram program f) := by
  exact Reference.IV04ConcreteOracleSearchProof.queriesAtMost_bindProgram first second program f hp hf

theorem executeCounting_result {α : Type} (program : Reference.IV04ConcreteOracleSearch.QueryProgram α) :
    (Reference.IV04ConcreteOracleSearch.executeCounting program).1=Reference.IV04ConcreteOracleSearch.execute program := by
  exact Reference.IV04ConcreteOracleSearchProof.executeCounting_result program

theorem executeCounting_bound {α : Type} (bound : ℕ) (program : Reference.IV04ConcreteOracleSearch.QueryProgram α)
    (h : Reference.IV04ConcreteOracleSearch.queriesAtMost bound program) : (Reference.IV04ConcreteOracleSearch.executeCounting program).2≤bound := by
  exact Reference.IV04ConcreteOracleSearchProof.executeCounting_bound bound program h

theorem natural_bits_value (n : ℕ) : wordValue n.bits=n := by
  exact Reference.IV04ConcreteOracleSearchProof.natural_bits_value n

theorem typed_certificate_denominator_bound {n : ℕ} (p : Fin n → ℤ) (d bound : ℕ)
    (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound) :
    d≤2^bound := by
  exact Reference.IV04ConcreteOracleSearchProof.typed_certificate_denominator_bound p d bound hlen

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
  exact Reference.IV04ConcreteOracleSearchProof.capped_threshold_certificate_coordinate_exact A b j p d hd hmax bound hlen lower upper hu hwidth certificate hcertlen haccept

theorem coordinateRecovery_query_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (bound fuel : ℕ) (lower upper : ℚ) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost (fuel+bound) (Reference.IV04ConcreteOracleSearch.coordinateRecovery A b j bound fuel lower upper) := by
  exact Reference.IV04ConcreteOracleSearchProof.coordinateRecovery_query_bound A b j bound fuel lower upper

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
  exact Reference.IV04ConcreteOracleSearchProof.coordinateRecovery_actual_output_exact A b j p d hd hx hmax bound hlen fuel lower upper hl hu hwidth

theorem actual_query_language_np : Reference.IV04ConcreteOracleSearch.cappedPrefixFeasibilityLanguage∈NP := by
  exact Reference.IV04ConcreteOracleSearchProof.actual_query_language_np

theorem actual_query_membership_exact (q : Reference.IV04ConcreteOracleSearch.PrefixQuery)
    (hbound : q.bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial q.instanceCode.length) :
    Reference.IV04ConcreteOracleSearch.encodedQuery q∈Reference.IV04ConcreteOracleSearch.cappedPrefixFeasibilityLanguage ↔ Reference.IV04ConcreteOracleSearch.prefixMembership q := by
  exact Reference.IV04ConcreteOracleSearchProof.actual_query_membership_exact q hbound

theorem instance_polynomial_mono (lower upper : ℕ) (h : lower≤upper) :
    Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial lower≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial upper := by
  exact Reference.IV04ConcreteOracleSearchProof.instance_polynomial_mono lower upper h

theorem capped_threshold_query_actual_np_membership {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n) (r : ℚ)
    (bound : ℕ) (hbound : bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length) :
    Reference.IV04ConcreteOracleSearch.encodedQuery (Reference.IV04ConcreteOracleSearch.cappedThresholdQuery A b j r bound)∈Reference.IV04ConcreteOracleSearch.cappedPrefixFeasibilityLanguage ↔
      Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.cappedThresholdQuery A b j r bound) := by
  exact Reference.IV04ConcreteOracleSearchProof.capped_threshold_query_actual_np_membership A b j r bound hbound

theorem encoded_query_length (q : Reference.IV04ConcreteOracleSearch.PrefixQuery) :
    (Reference.IV04ConcreteOracleSearch.encodedQuery q).length=2*q.instanceCode.length+2*q.bound+q.stem.length+4 := by
  exact Reference.IV04ConcreteOracleSearchProof.encoded_query_length q

theorem typed_certificate_numerator_bound {n : ℕ} (p : Fin n → ℤ) (d bound : ℕ)
    (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound) :
    ∀ j, |p j|≤((2^bound : ℕ) : ℤ) := by
  exact Reference.IV04ConcreteOracleSearchProof.typed_certificate_numerator_bound p d bound hlen

theorem typed_certificate_initial_bracket {n : ℕ} (p : Fin n → ℤ) (d bound : ℕ)
    (hd : 0<d) (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound)
    (j : Fin n) :
    ((-((2 : ℚ)^bound) : ℚ) : ℝ)≤(p j : ℝ)/(d : ℝ) ∧
      (p j : ℝ)/(d : ℝ)≤((2 : ℚ)^bound : ℝ) := by
  exact Reference.IV04ConcreteOracleSearchProof.typed_certificate_initial_bracket p d bound hd hlen j

theorem automatic_width_strict (bound : ℕ) :
    ((2 : ℚ)^bound-(-((2 : ℚ)^bound)))/2^(3*bound+2)<
      1/((2^bound : ℕ) : ℚ)^2 := by
  exact Reference.IV04ConcreteOracleSearchProof.automatic_width_strict bound

theorem boundedCoordinateRecovery_actual_query_count {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n) (bound : ℕ) :
    (Reference.IV04ConcreteOracleSearch.executeCounting (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)).2≤4*bound+2 := by
  exact Reference.IV04ConcreteOracleSearchProof.boundedCoordinateRecovery_actual_query_count A b j bound

theorem boundedCoordinateRecovery_actual_output_exact {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (p : Fin n → ℤ) (d : ℕ) (hd : 0<d)
    (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) (fun k => (p k : ℝ)/(d : ℝ)))
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤(p j : ℝ)/(d : ℝ))
    (bound : ℕ) (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound) :
    Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)=some ((p j : ℚ)/(d : ℚ)) := by
  exact Reference.IV04ConcreteOracleSearchProof.boundedCoordinateRecovery_actual_output_exact A b j p d hd hx hmax bound hlen

theorem integer_tight_point_sharp_positive_common_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (x : Fin n → ℝ) (H : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (hkernel : ∀ d : Fin n → ℝ,
      (∀ i ∈ tightRows (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x,
        (Reference.IV04ConcreteOracleSearch.integerRealMatrix A *ᵥ d) i=0) → d=0) :
    ∃ p : Fin n → ℤ, ∃ d : ℕ, 0<d ∧ d≤Reference.IV04ConcreteOracleSearch.sharpCertificateBound n H ∧
      (∀ j, |p j|≤(Reference.IV04ConcreteOracleSearch.sharpCertificateBound n H : ℤ)) ∧
      ∀ j, x j=(p j : ℝ)/(d : ℝ) := by
  exact Reference.IV04ConcreteOracleSearchProof.integer_tight_point_sharp_positive_common_certificate A b x H hA hb hkernel

theorem actual_original_optimum_polynomial_certificate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) (j : Fin n)
    (hne : ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hline : lineFree (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)) (upper : ℝ)
    (hupper : ∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤upper) :
    ∃ p : Fin n → ℤ, ∃ d : ℕ, 0<d ∧
      feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) (fun k => (p k : ℝ)/(d : ℝ)) ∧
      (∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤(p j : ℝ)/(d : ℝ)) ∧
      (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤
        Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length := by
  exact Reference.IV04ConcreteOracleSearchProof.actual_original_optimum_polynomial_certificate A b hm j hne hline upper hupper

theorem actual_bounded_coordinate_recovery {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) (j : Fin n)
    (hne : ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hline : lineFree (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)) (upper : ℝ)
    (hupper : ∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤upper) :
    let bound := Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length
    ∃ maximum : ℚ, Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)=some maximum ∧
      (∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x ∧ x j=(maximum : ℝ)) ∧
      (∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤(maximum : ℝ)) ∧
      (Reference.IV04ConcreteOracleSearch.executeCounting (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)).2≤4*bound+2 := by
  exact Reference.IV04ConcreteOracleSearchProof.actual_bounded_coordinate_recovery A b hm j hne hline upper hupper

theorem selfReduce_query_caps (instanceCode : List Bool) (bound fuel : ℕ)
    (stem : List Bool) (hcap : bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial instanceCode.length) :
    Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound fuel stem) := by
  exact Reference.IV04ConcreteOracleSearchProof.selfReduce_query_caps instanceCode bound fuel stem hcap

theorem cappedBinarySearch_query_caps {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (bound fuel : ℕ) (lower upper : ℚ)
    (hcap : bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length) :
    Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound fuel lower upper) := by
  exact Reference.IV04ConcreteOracleSearchProof.cappedBinarySearch_query_caps A b j bound fuel lower upper hcap

theorem bindProgram_query_caps {α β : Type} (program : Reference.IV04ConcreteOracleSearch.QueryProgram α)
    (f : α → Reference.IV04ConcreteOracleSearch.QueryProgram β) (hp : Reference.IV04ConcreteOracleSearch.queryCapsValid program) (hf : ∀ a, Reference.IV04ConcreteOracleSearch.queryCapsValid (f a)) :
    Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.bindProgram program f) := by
  exact Reference.IV04ConcreteOracleSearchProof.bindProgram_query_caps program f hp hf

theorem coordinateRecovery_query_caps {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (bound fuel : ℕ) (lower upper : ℚ)
    (hcap : bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length) :
    Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.coordinateRecovery A b j bound fuel lower upper) := by
  exact Reference.IV04ConcreteOracleSearchProof.coordinateRecovery_query_caps A b j bound fuel lower upper hcap

theorem executeActualNP_exact {α : Type} (program : Reference.IV04ConcreteOracleSearch.QueryProgram α) (hcap : Reference.IV04ConcreteOracleSearch.queryCapsValid program) :
    Reference.IV04ConcreteOracleSearch.executeActualNP program=Reference.IV04ConcreteOracleSearch.executeCounting program := by
  exact Reference.IV04ConcreteOracleSearchProof.executeActualNP_exact program hcap

theorem actual_np_bounded_coordinate_recovery {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) (j : Fin n)
    (hne : ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hline : lineFree (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)) (upper : ℝ)
    (hupper : ∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤upper) :
    let bound := Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length
    ∃ maximum : ℚ, (Reference.IV04ConcreteOracleSearch.executeActualNP (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)).1=some maximum ∧
      (∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x ∧ x j=(maximum : ℝ)) ∧
      (∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤(maximum : ℝ)) ∧
      (Reference.IV04ConcreteOracleSearch.executeActualNP (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)).2≤4*bound+2 := by
  exact Reference.IV04ConcreteOracleSearchProof.actual_np_bounded_coordinate_recovery A b hm j hne hline upper hupper


#print axioms prefix_length_le_of_membership

#print axioms prefix_membership_child

#print axioms prefix_membership_at_bound

#print axioms selfReduce_query_bound

#print axioms selfReduce_recovers_certificate

#print axioms bounded_certificate_self_reduction

#print axioms actual_feasibility_certificate_search

#print axioms threshold_feasible_iff

#print axioms threshold_query_membership_iff

#print axioms threshold_membership_iff_le_actual_optimum

#print axioms binarySearch_query_bound

#print axioms binarySearch_actual_optimum_bracket

#print axioms payloadNth_code

#print axioms natural_fraction_den_le

#print axioms accepted_certificate_point

#print axioms capped_threshold_membership_iff_actual_optimum

#print axioms original_instance_length_le_threshold

#print axioms cappedBinarySearch_query_bound

#print axioms cappedBinarySearch_actual_optimum_bracket

#print axioms execute_bindProgram

#print axioms queriesAtMost_mono

#print axioms queriesAtMost_bindProgram

#print axioms executeCounting_result

#print axioms executeCounting_bound

#print axioms natural_bits_value

#print axioms typed_certificate_denominator_bound

#print axioms capped_threshold_certificate_coordinate_exact

#print axioms coordinateRecovery_query_bound

#print axioms coordinateRecovery_actual_output_exact

#print axioms actual_query_language_np

#print axioms actual_query_membership_exact

#print axioms instance_polynomial_mono

#print axioms capped_threshold_query_actual_np_membership

#print axioms encoded_query_length

#print axioms typed_certificate_numerator_bound

#print axioms typed_certificate_initial_bracket

#print axioms automatic_width_strict

#print axioms boundedCoordinateRecovery_actual_query_count

#print axioms boundedCoordinateRecovery_actual_output_exact

#print axioms integer_tight_point_sharp_positive_common_certificate

#print axioms actual_original_optimum_polynomial_certificate

#print axioms actual_bounded_coordinate_recovery

#print axioms selfReduce_query_caps

#print axioms cappedBinarySearch_query_caps

#print axioms bindProgram_query_caps

#print axioms coordinateRecovery_query_caps

#print axioms executeActualNP_exact

#print axioms actual_np_bounded_coordinate_recovery
end Reference.IV04ConcreteOracleSearch
