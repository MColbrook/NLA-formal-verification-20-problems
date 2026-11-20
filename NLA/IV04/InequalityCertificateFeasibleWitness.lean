module

public import NLA.IV04.InequalityCertificateNormalization
public import NLA.IV04.InequalityCertificateLengths
public import NLA.IV04.InequalityCertificateMatrixSemantics

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
namespace IV04.Paper.InequalityCertificate
noncomputable section

def inequalityWitnessExponent (m n L : ℕ) : ℕ := n*n+n*(m+n+2*L)
def inequalityWitnessLengthBound (m n L : ℕ) : ℕ :=
  (4*n+1)*(inequalityWitnessExponent m n L+3)

theorem exists_positive_feasible_certificate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (H : ℕ)
    (hA : ∀ i j, |A i j|≤(H : ℤ)) (hb : ∀ i, |b i|≤(H : ℤ))
    (hH : 1≤H) (hne : ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x) :
    ∃ p : Fin n → ℤ, ∃ d : ℕ,
      0<d ∧ d≤gramCertificateBound (m+n) n H ∧
      (∀ j, |p j|≤(gramCertificateBound (m+n) n H : ℤ)) ∧
      feasible (integerRealMatrix A) (integerRealVector b)
        (fun j => (p j : ℝ)/(d : ℝ)) := by
  classical
  obtain ⟨x,hx⟩ := hne
  let s : Fin n → ℤ := fun j => if 0≤x j then 1 else -1
  have hs : ∀ j, s j≠0 := by
    intro j
    dsimp [s]
    split_ifs <;> norm_num
  have hsH : ∀ j, |s j|≤(H : ℤ) := by
    intro j
    have hcast : (1 : ℤ)≤(H : ℤ) := by exact_mod_cast hH
    dsimp [s]
    split_ifs <;> simpa using hcast
  have hsigned : (signedFeasibleSet (integerRealMatrix A) (integerRealVector b)
      (integerRealVector s)).Nonempty := by
    refine ⟨x,hx,?_⟩
    intro j
    change 0≤(s j : ℝ)*x j
    dsimp [s]
    by_cases hj : 0≤x j
    · simp [hj]
    · simp only [if_neg hj,Int.cast_neg,Int.cast_one,neg_one_mul]
      exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hj))
  obtain ⟨y,hy,p,d,hd,hdQ,hpQ,hyeq⟩ :=
    exists_bounded_signed_orthant_extreme_certificate A b s H hA hb hs hsH hsigned
  have hyset : y ∈ signedFeasibleSet (integerRealMatrix A) (integerRealVector b)
      (integerRealVector s) := hy.1
  obtain ⟨q,e,he,heQ,hqQ,hyq⟩ := normalize_common_denominator y p d
    (gramCertificateBound (m+n) n H) hd (by simpa using hdQ) (by simpa using hpQ) hyeq
  refine ⟨q,e,he,heQ,hqQ,?_⟩
  have heq : y=(fun j => (q j : ℝ)/(e : ℝ)) := funext hyq
  rw [← heq]
  exact hyset.1

theorem exists_polynomial_encoded_feasible_certificate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (L : ℕ)
    (hA : ∀ i j, |A i j|≤((2^L : ℕ) : ℤ))
    (hb : ∀ i, |b i|≤((2^L : ℕ) : ℤ))
    (hne : ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x) :
    ∃ p : Fin n → ℤ, ∃ d : ℕ,
      0<d ∧ d≤2^(inequalityWitnessExponent m n L) ∧
      (∀ j, |p j|≤((2^(inequalityWitnessExponent m n L) : ℕ) : ℤ)) ∧
      (inequalityIntegerCertificateCode (integerVectorList p) d).length≤
        inequalityWitnessLengthBound m n L ∧
      polynomialInequalitySystemVerifier
        (inequalityIntegerSystemCode (integerMatrixRows A b) (integerVectorList p) d)=[true] := by
  obtain ⟨p,d,hd,hdQ,hpQ,hfeasible⟩ := exists_positive_feasible_certificate A b (2^L) hA hb
    (Nat.one_le_two_pow) hne
  have hQ : gramCertificateBound (m+n) n (2^L)≤2^(inequalityWitnessExponent m n L) := by
    exact gramCertificateBound_le_two_pow (m+n) n (2^L) L (le_refl _)
  have hdP := hdQ.trans hQ
  have hpP : ∀ j, |p j|≤((2^(inequalityWitnessExponent m n L) : ℕ) : ℤ) := by
    intro j
    exact (hpQ j).trans (by exact_mod_cast hQ)
  refine ⟨p,d,hd,hdP,hpP,?_,?_⟩
  · have hpList : ∀ z ∈ integerVectorList p,
        |z|≤((2^(inequalityWitnessExponent m n L) : ℕ) : ℤ) := by
      intro z hz
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
      exact hpP j
    simpa only [inequalityWitnessLengthBound,integerVectorList,List.length_ofFn] using
      integer_certificate_length_bound (integerVectorList p) d (inequalityWitnessExponent m n L) hpList hdP
  · exact (integer_matrix_verifier_exact A b p d).mpr ⟨hd,hfeasible⟩

theorem feasible_iff_bounded_verifier_certificate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (L : ℕ)
    (hA : ∀ i j, |A i j|≤((2^L : ℕ) : ℤ))
    (hb : ∀ i, |b i|≤((2^L : ℕ) : ℤ)) :
    (∃ x, feasible (integerRealMatrix A) (integerRealVector b) x) ↔
    ∃ p : Fin n → ℤ, ∃ d : ℕ,
      (inequalityIntegerCertificateCode (integerVectorList p) d).length≤
        inequalityWitnessLengthBound m n L ∧
      polynomialInequalitySystemVerifier
        (inequalityIntegerSystemCode (integerMatrixRows A b) (integerVectorList p) d)=[true] := by
  constructor
  · intro hne
    obtain ⟨p,d,_,_,_,hlen,haccept⟩ := exists_polynomial_encoded_feasible_certificate A b L hA hb hne
    exact ⟨p,d,hlen,haccept⟩
  · rintro ⟨p,d,_,haccept⟩
    exact ⟨_,((integer_matrix_verifier_exact A b p d).mp haccept).2⟩

theorem actual_fp_and_bounded_feasibility_certificates {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (L : ℕ)
    (hA : ∀ i j, |A i j|≤((2^L : ℕ) : ℤ))
    (hb : ∀ i, |b i|≤((2^L : ℕ) : ℤ)) :
    polynomialInequalitySystemVerifier ∈ FP ∧
    ((∃ x, feasible (integerRealMatrix A) (integerRealVector b) x) ↔
      ∃ p : Fin n → ℤ, ∃ d : ℕ,
        (inequalityIntegerCertificateCode (integerVectorList p) d).length≤
          inequalityWitnessLengthBound m n L ∧
        polynomialInequalitySystemVerifier
          (inequalityIntegerSystemCode (integerMatrixRows A b) (integerVectorList p) d)=[true]) := by
  exact ⟨inequality_system_verifier_mem_fp,feasible_iff_bounded_verifier_certificate A b L hA hb⟩

#print axioms exists_positive_feasible_certificate
#print axioms exists_polynomial_encoded_feasible_certificate
#print axioms feasible_iff_bounded_verifier_certificate
#print axioms actual_fp_and_bounded_feasibility_certificates
end
end IV04.Paper.InequalityCertificate
