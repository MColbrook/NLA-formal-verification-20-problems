module

public import NLA.IV04.ConcreteOracleSearchProof.CertificatePoint

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open Complexity IV04.Paper.Computational IV04.Paper.InequalityCertificate
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem capped_threshold_membership_iff_actual_optimum {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (p : Fin n → ℤ) (d : ℕ) (hd : 0<d)
    (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) (fun k => (p k : ℝ)/(d : ℝ)))
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤(p j : ℝ)/(d : ℝ))
    (bound : ℕ)
    (hlen : (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤bound)
    (r : ℚ) : Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.cappedThresholdQuery A b j r bound) ↔
      (r : ℝ)≤(p j : ℝ)/(d : ℝ) := by
  constructor
  · rintro ⟨certificate,_,haccept⟩
    rw [Reference.IV04ConcreteOracleSearchProof.accepted_certificate_frozen] at haccept
    obtain ⟨y,hy⟩ := arbitrary_certificate_sound (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r) (Reference.IV04ConcreteOracleSearch.thresholdBounds b r)
      (by omega) certificate haccept
    obtain ⟨hyfeas,hyr⟩ := (Reference.IV04ConcreteOracleSearchProof.threshold_feasible_iff A b j r y).mp hy
    exact hyr.trans (hmax y hyfeas)
  · intro hr
    have haug := (Reference.IV04ConcreteOracleSearchProof.threshold_feasible_iff A b j r (fun k => (p k : ℝ)/(d : ℝ))).mpr ⟨hx,hr⟩
    have ha := (integer_matrix_verifier_exact (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r) (Reference.IV04ConcreteOracleSearch.thresholdBounds b r) p d).mpr ⟨hd,haug⟩
    rw [integer_matrix_code_framing] at ha
    exact ⟨Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d,hlen,
      (Reference.IV04ConcreteOracleSearchProof.accepted_certificate_frozen _ _).mpr ha⟩

theorem original_instance_length_le_threshold {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n) (r : ℚ) :
    (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length≤
      (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r) (Reference.IV04ConcreteOracleSearch.thresholdBounds b r)).length := by
  simp only [Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode,List.ofFn_succ,payloadListCode,pair_length]
  have he : (List.ofFn (fun i : Fin m =>
      Reference.IV04ConcreteOracleSearch.integerMatrixRowCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r) (Reference.IV04ConcreteOracleSearch.thresholdBounds b r) i.succ))=
      List.ofFn (Reference.IV04ConcreteOracleSearch.integerMatrixRowCode A b) := by
    congr 1
  rw [he]
  omega

#print axioms capped_threshold_membership_iff_actual_optimum

#print axioms original_instance_length_le_threshold
end Reference.IV04ConcreteOracleSearchProof
