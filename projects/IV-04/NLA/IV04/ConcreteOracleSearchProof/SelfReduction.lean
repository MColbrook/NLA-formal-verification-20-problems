module

public import NLA.IV04.ConcreteOracleSearchProof.Prefix

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof

open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem selfReduce_query_bound (instanceCode : List Bool) (bound fuel : ℕ)
    (stem : List Bool) : Reference.IV04ConcreteOracleSearch.queriesAtMost fuel (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound fuel stem) := by
  induction fuel generalizing stem with
  | zero => simp [Reference.IV04ConcreteOracleSearch.selfReduce,Reference.IV04ConcreteOracleSearch.queriesAtMost]
  | succ fuel ih =>
    unfold Reference.IV04ConcreteOracleSearch.selfReduce
    split_ifs
    · trivial
    · intro answer
      exact ih _

theorem selfReduce_recovers_certificate (instanceCode : List Bool) (bound fuel : ℕ)
    (stem : List Bool)
    (h : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem⟩)
    (hspace : bound≤stem.length+fuel) :
    ∃ certificate, Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound fuel stem)=some certificate ∧
      certificate.length≤bound ∧ Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate := by
  classical
  induction fuel generalizing stem with
  | zero =>
    have ha := Reference.IV04ConcreteOracleSearchProof.prefix_membership_at_bound instanceCode bound stem h (by simpa using hspace)
    exact ⟨stem,by simp [Reference.IV04ConcreteOracleSearch.selfReduce,Reference.IV04ConcreteOracleSearch.execute,ha],
      Reference.IV04ConcreteOracleSearchProof.prefix_length_le_of_membership _ _ _ h,ha⟩
  | succ fuel ih =>
    by_cases ha : Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode stem
    · exact ⟨stem,by simp [Reference.IV04ConcreteOracleSearch.selfReduce,Reference.IV04ConcreteOracleSearch.execute,ha],
        Reference.IV04ConcreteOracleSearchProof.prefix_length_le_of_membership _ _ _ h,ha⟩
    · obtain hc | hc := Reference.IV04ConcreteOracleSearchProof.prefix_membership_child instanceCode bound stem h ha
      · have hs : bound≤(stem++[false]).length+fuel := by
          simp only [List.length_append,List.length_singleton]
          omega
        obtain ⟨certificate,he,hlen,haccept⟩ := ih (stem++[false]) hc hs
        refine ⟨certificate,?_,hlen,haccept⟩
        simpa [Reference.IV04ConcreteOracleSearch.selfReduce,Reference.IV04ConcreteOracleSearch.execute,ha,hc] using he
      · by_cases hf : Reference.IV04ConcreteOracleSearch.prefixMembership ⟨instanceCode,bound,stem++[false]⟩
        · have hs : bound≤(stem++[false]).length+fuel := by
            simp only [List.length_append,List.length_singleton]
            omega
          obtain ⟨certificate,he,hlen,haccept⟩ := ih (stem++[false]) hf hs
          refine ⟨certificate,?_,hlen,haccept⟩
          simpa [Reference.IV04ConcreteOracleSearch.selfReduce,Reference.IV04ConcreteOracleSearch.execute,ha,hf] using he
        · have hs : bound≤(stem++[true]).length+fuel := by
            simp only [List.length_append,List.length_singleton]
            omega
          obtain ⟨certificate,he,hlen,haccept⟩ := ih (stem++[true]) hc hs
          refine ⟨certificate,?_,hlen,haccept⟩
          simpa [Reference.IV04ConcreteOracleSearch.selfReduce,Reference.IV04ConcreteOracleSearch.execute,ha,hf] using he

theorem bounded_certificate_self_reduction (instanceCode : List Bool) (bound : ℕ)
    (h : ∃ certificate : List Bool, certificate.length≤bound ∧
      Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate) :
    Reference.IV04ConcreteOracleSearch.queriesAtMost bound (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound bound []) ∧
    ∃ certificate, Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound bound [])=some certificate ∧
      certificate.length≤bound ∧ Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate := by
  refine ⟨Reference.IV04ConcreteOracleSearchProof.selfReduce_query_bound _ _ _ _,?_⟩
  apply Reference.IV04ConcreteOracleSearchProof.selfReduce_recovers_certificate
  · obtain ⟨certificate,hlen,haccept⟩ := h
    exact ⟨certificate,by simpa using hlen,by simpa using haccept⟩
  · simp

#print axioms selfReduce_query_bound

#print axioms selfReduce_recovers_certificate

#print axioms bounded_certificate_self_reduction
end Reference.IV04ConcreteOracleSearchProof
