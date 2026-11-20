module

public import NLA.TR27.PaperProduct

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem tensor_raw_mem_span (k : ℕ) (Y : Set (ℙ ℂ (⨂[ℂ] _ : Fin k, W)))
    (w : Fin k → W) (q : Fin k → ℙ ℂ W) (hq : ∀ i, Represents (w i) (q i))
    (hY : tensorPoint k q ∈ Y) :
    PiTensorProduct.tprod ℂ w ∈ Submodule.span ℂ (Projectivization.rep '' Y) := by
  choose a ha heq using hq
  have hmem : PiTensorProduct.tprod ℂ (fun i => (q i).rep) ∈
      Submodule.span ℂ (Projectivization.rep '' Y) :=
    (projective_span_mk Y _ (tensor_reps_nonzero k q)).mp
      (Projectivization.Subspace.subset_span Y hY)
  have ht : PiTensorProduct.tprod ℂ (fun i => (q i).rep) =
      (∏ i, a i) • PiTensorProduct.tprod ℂ w := by
    simp_rw [heq]
    exact MultilinearMap.map_smul_univ _ _ _
  rw [ht] at hmem
  exact (Submodule.smul_mem_iff _ (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))).mp hmem

/-- A sum of L powers of n-term combinations uses at most L*n^k full
Segre points. No nonzero assumption is made on any intermediate combination. -/
theorem projective_power_mixture_upper (X : Set (ℙ ℂ W)) (p : ℙ ℂ W)
    (v : W) (hp : Represents v p) (L n k : ℕ)
    (z : Fin L → W) (w : Fin L → Fin n → W)
    (a : Fin L → Fin n → ℂ) (b : Fin L → ℂ)
    (q : Fin L → Fin n → ℙ ℂ W)
    (hq : ∀ l j, Represents (w l j) (q l j)) (hX : ∀ l j, q l j ∈ X)
    (hz : ∀ l, z l = ∑ j, a l j • w l j)
    (havg : PiTensorProduct.tprod ℂ (fun _ : Fin k => v) =
      ∑ l, b l • PiTensorProduct.tprod ℂ (fun _ : Fin k => z l)) :
    ProjectiveRankAtMost (productPoints X k) (L*n^k) (powerPoint p k) := by
  let e := (Fintype.equivFin (Fin L × (Fin k → Fin n))).symm
  let terms : Fin (Fintype.card (Fin L × (Fin k → Fin n))) →
      ℙ ℂ (⨂[ℂ] _ : Fin k, W) :=
    fun l => tensorPoint k (fun i => q (e l).1 ((e l).2 i))
  refine ⟨_, ?_, terms, ?_, ?_⟩
  · simp
  · intro l
    exact ⟨_, (fun i => hX _ _), represents_mk _ _⟩
  · change Projectivization.mk ℂ (PiTensorProduct.tprod ℂ (fun _ : Fin k => p.rep)) _ ∈ _
    rw [projective_span_mk]
    obtain ⟨c, hc, hrep⟩ := hp
    simp_rw [hrep]
    rw [MultilinearMap.map_smul_univ]
    apply Submodule.smul_mem
    rw [havg]
    apply Submodule.sum_mem
    intro l _
    apply Submodule.smul_mem
    simp_rw [hz l]
    rw [MultilinearMap.map_sum]
    apply Submodule.sum_mem
    intro t _
    rw [MultilinearMap.map_smul_univ]
    apply Submodule.smul_mem
    apply tensor_raw_mem_span k (Set.range terms) _ (fun i => q l (t i))
      (fun i => hq l (t i))
    refine ⟨e.symm (l,t), ?_⟩
    simp [terms]

#print axioms projective_power_mixture_upper
end NLA.TR27.Paper
