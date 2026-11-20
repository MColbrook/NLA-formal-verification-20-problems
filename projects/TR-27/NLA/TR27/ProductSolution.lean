module

public import NLA.TR27.PaperProduct

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization Classical
namespace NLA.TR27.Paper
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem paper_finite_rank_semantics (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) (r : ℕ) :
    IsLeast {n | ProjectiveRankAtMost X n p} r ↔
      projectiveRank X p = r ∧ ∃ n, ProjectiveRankAtMost X n p := by
  constructor
  · intro h
    exact ⟨h.csInf_eq, ⟨r, h.1⟩⟩
  · rintro ⟨hr, hex⟩
    have hm : ProjectiveRankAtMost X (projectiveRank X p) p := csInf_mem hex
    refine ⟨hr ▸ hm, ?_⟩
    intro n hn
    rw [← hr]
    exact csInf_le' hn

theorem paper_product_rank (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) (r K k : ℕ)
    (hK : 1 ≤ K) (hk : 1 ≤ k)
    (hR : IsLeast {n | ProjectiveRankAtMost X n p} r)
    (hind : ∀ s : Finset (ℙ ℂ W), s.card ≤ K → (∀ q ∈ s, q ∈ X) →
      LinearIndependent ℂ (fun q : s => (q : ℙ ℂ W).rep))
    (hbound : r ^ k - 1 ≤ K) :
    projectiveRank (productPoints X k) (powerPoint p k) = r ^ k := by
  exact projective_power_rank_value X p r K k hR hind hbound

theorem paper_product_attained_minimum (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) (r K k : ℕ)
    (hK : 1 ≤ K) (hk : 1 ≤ k)
    (hR : IsLeast {n | ProjectiveRankAtMost X n p} r)
    (hind : ∀ s : Finset (ℙ ℂ W), s.card ≤ K → (∀ q ∈ s, q ∈ X) →
      LinearIndependent ℂ (fun q : s => (q : ℙ ℂ W).rep))
    (hbound : r ^ k - 1 ≤ K) :
    IsLeast {n | ProjectiveRankAtMost (productPoints X k) n (powerPoint p k)} (r ^ k) := by
  exact projective_power_rank X p r K k hR hind hbound

#print axioms paper_finite_rank_semantics
#print axioms paper_product_rank
#print axioms paper_product_attained_minimum

end NLA.TR27.Paper
