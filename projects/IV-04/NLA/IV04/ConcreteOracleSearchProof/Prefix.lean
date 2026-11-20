module

public import NLA.IV04.ConcreteOracleSearchDefinitions

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof

open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem prefix_length_le_of_membership (instanceCode : List Bool) (bound : ℕ)
    (stem : List Bool) (h : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem⟩) :
    stem.length≤bound := by
  obtain ⟨tail,hlen,_⟩ := h
  simp only [List.length_append] at hlen
  omega

theorem prefix_membership_child (instanceCode : List Bool) (bound : ℕ)
    (stem : List Bool)
    (h : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem⟩)
    (hnot : ¬Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode stem) :
    Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem++[false]⟩ ∨
    Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem++[true]⟩ := by
  obtain ⟨tail,hlen,haccept⟩ := h
  cases tail with
  | nil => exact False.elim (hnot (by simpa using haccept))
  | cons bit rest =>
    cases bit
    · left
      exact ⟨rest,by simpa [List.append_assoc] using hlen,
        by simpa [List.append_assoc] using haccept⟩
    · right
      exact ⟨rest,by simpa [List.append_assoc] using hlen,
        by simpa [List.append_assoc] using haccept⟩

theorem prefix_membership_at_bound (instanceCode : List Bool) (bound : ℕ)
    (stem : List Bool)
    (h : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem⟩) (hbound : bound≤stem.length) :
    Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode stem := by
  obtain ⟨tail,hlen,haccept⟩ := h
  have hnil : tail=[] := by
    cases tail with
    | nil => rfl
    | cons bit rest =>
      simp only [List.length_append,List.length_cons] at hlen
      omega
  simpa only [hnil,List.append_nil] using haccept

#print axioms prefix_length_le_of_membership

#print axioms prefix_membership_child

#print axioms prefix_membership_at_bound
end Reference.IV04ConcreteOracleSearchProof
