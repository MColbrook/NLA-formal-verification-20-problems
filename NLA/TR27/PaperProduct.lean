module

public import NLA.TR27.PaperProductDefinitions
public import NLA.TR27.PaperTensorLower

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization Classical
namespace NLA.TR27.Paper
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem projective_power_upper (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) (r k : ℕ)
    (hr : ProjectiveRankAtMost X r p) :
    ProjectiveRankAtMost (productPoints X k) (r ^ k) (powerPoint p k) := by
  classical
  obtain ⟨n, hn, q, hq, hspan⟩ := hr
  have hmem : p.rep ∈ Submodule.span ℂ (Set.range (fun i => (q i).rep)) := by
    simpa only [← Set.range_comp, Function.comp_def] using (projective_span_rep _ _).mp hspan
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  let e := (Fintype.equivFin (Fin k → Fin n)).symm
  let terms : Fin (Fintype.card (Fin k → Fin n)) → ℙ ℂ (⨂[ℂ] _ : Fin k, W) :=
    fun l => tensorPoint k (fun i => q (e l i))
  refine ⟨Fintype.card (Fin k → Fin n), ?_, terms, ?_, ?_⟩
  · simpa using Nat.pow_le_pow_left hn k
  · intro l
    exact ⟨(fun i => q (e l i)), (fun i => hq _), represents_mk _ _⟩
  · change Projectivization.mk ℂ (PiTensorProduct.tprod ℂ (fun _ : Fin k => p.rep)) _ ∈ _
    rw [projective_span_mk]
    have hsum : PiTensorProduct.tprod ℂ (fun _ : Fin k => p.rep) =
        ∑ t : Fin k → Fin n, (∏ i, a (t i)) •
          PiTensorProduct.tprod ℂ (fun i => (q (t i)).rep) := by
      conv_lhs => enter [2]; intro i; rw [← ha]
      rw [MultilinearMap.map_sum]
      apply Finset.sum_congr rfl
      intro t _
      exact MultilinearMap.map_smul_univ _ _ _
    rw [hsum]
    apply Submodule.sum_mem
    intro t _
    apply Submodule.smul_mem
    apply (projective_span_mk (Set.range terms) _ (tensor_reps_nonzero k (fun i => q (t i)))).mp
    apply Projectivization.Subspace.subset_span
    refine ⟨e.symm t, ?_⟩
    simp [terms, tensorPoint]

/-- Attained minimal rank is preserved multiplicatively through k tensor factors
when all sets of at most K curve points are independent. -/
theorem projective_power_rank (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) (r K k : ℕ)
    (hR : IsLeast {n | ProjectiveRankAtMost X n p} r)
    (hind : ∀ s : Finset (ℙ ℂ W), s.card ≤ K → (∀ q ∈ s, q ∈ X) →
      LinearIndependent ℂ (fun q : s => (q : ℙ ℂ W).rep))
    (hbound : r ^ k - 1 ≤ K) :
    IsLeast {n | ProjectiveRankAtMost (productPoints X k) n (powerPoint p k)} (r ^ k) := by
  classical
  refine ⟨projective_power_upper X p r k hR.1, ?_⟩
  intro L hL
  by_contra hsmall
  have hLlt : L < r ^ k := lt_of_not_ge hsmall
  obtain ⟨n, hn, q, hq, hspan⟩ := hL
  have hmin : ∀ l < r, ¬ ProjectiveRankAtMost X l p := by
    intro l hl hmem
    exact (not_lt_of_ge (hR.2 hmem)) hl
  have hspan' : Projectivization.mk ℂ
      (PiTensorProduct.tprod ℂ (fun _ : Fin k => p.rep)) _ ∈
      Projectivization.Subspace.span (Set.range q) := hspan
  obtain ⟨a, ha⟩ := (projective_span_range n q _ _).mp hspan'
  choose x hx c hc hrep using hq
  have heq : PiTensorProduct.tprod ℂ (fun _ : Fin k => p.rep) =
      ∑ l, (a l * c l) • PiTensorProduct.tprod ℂ (fun i => (x l i).rep) := by
    rw [ha]
    apply Finset.sum_congr rfl
    intro l _
    rw [hrep l, smul_smul]
  have hlower := projective_tensor_decomposition_lower X p r K k n hmin hind
    (by omega) (fun l => a l * c l) x hx heq
  omega

theorem projective_power_rank_value (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) (r K k : ℕ)
    (hR : IsLeast {n | ProjectiveRankAtMost X n p} r)
    (hind : ∀ s : Finset (ℙ ℂ W), s.card ≤ K → (∀ q ∈ s, q ∈ X) →
      LinearIndependent ℂ (fun q : s => (q : ℙ ℂ W).rep))
    (hbound : r ^ k - 1 ≤ K) :
    projectiveRank (productPoints X k) (powerPoint p k) = r ^ k :=
  (projective_power_rank X p r K k hR hind hbound).csInf_eq

#print axioms projective_power_rank_value
end NLA.TR27.Paper
