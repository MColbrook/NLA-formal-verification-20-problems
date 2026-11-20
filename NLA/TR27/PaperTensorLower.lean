module

public import NLA.TR27.PaperTensorSupport
public import NLA.TR27.Semantics

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization Classical
namespace NLA.TR27.Paper
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Minimal projective rank bounds the support of every curve-point expansion. -/
theorem projective_expansion_support {κ : Type*} [Fintype κ]
    (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) (r : ℕ)
    (hmin : ∀ L < r, ¬ ProjectiveRankAtMost X L p)
    (q : κ → ℙ ℂ W) (hq : ∀ j, q j ∈ X) (a : κ → ℂ)
    (ha : p.rep = ∑ j, a j • (q j).rep) :
    r ≤ (Finset.univ.filter (fun j => a j ≠ 0)).card := by
  classical
  let s : Finset κ := Finset.univ.filter (fun j => a j ≠ 0)
  let e := (Fintype.equivFin s).symm
  by_contra hr
  have hs : Fintype.card s < r := by
    rw [Fintype.card_coe]
    exact lt_of_not_ge hr
  apply hmin (Fintype.card s) hs
  refine ⟨Fintype.card s, le_rfl, (fun i => q (e i)), (fun i => hq _), ?_⟩
  rw [projective_span_rep, ha]
  have heq : (∑ j, a j • (q j).rep) = ∑ j ∈ s, a j • (q j).rep := by
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : a j = 0 <;> simp [hj]
  rw [heq]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨q j, ?_, rfl⟩
  exact ⟨e.symm ⟨j, hj⟩, by simp⟩

/-- The lower bound in the paper's general product lemma, for a completely
arbitrary short decomposition with unrelated choices in each factor. -/
theorem projective_tensor_decomposition_lower
    (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) (r K k L : ℕ)
    (hmin : ∀ n < r, ¬ ProjectiveRankAtMost X n p)
    (hind : ∀ s : Finset (ℙ ℂ W), s.card ≤ K → (∀ q ∈ s, q ∈ X) →
      LinearIndependent ℂ (fun q : s => (q : ℙ ℂ W).rep))
    (hLK : L ≤ K) (b : Fin L → ℂ) (q : Fin L → Fin k → ℙ ℂ W)
    (hq : ∀ l i, q l i ∈ X)
    (h : PiTensorProduct.tprod ℂ (fun _ : Fin k => p.rep) =
      ∑ l, b l • PiTensorProduct.tprod ℂ (fun i => (q l i).rep)) :
    r ^ k ≤ L := by
  classical
  let s : Fin k → Finset (ℙ ℂ W) := fun i => Finset.univ.image (fun l => q l i)
  have hmem (l : Fin L) (i : Fin k) : q l i ∈ s i :=
    Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  have hX (i : Fin k) (z : s i) : (z : ℙ ℂ W) ∈ X := by
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp z.property
    rw [← hl]
    exact hq l i
  have hli (i : Fin k) : LinearIndependent ℂ (fun z : s i => (z : ℙ ℂ W).rep) := by
    apply hind (s i) ((Finset.card_image_le.trans (by simp)).trans hLK)
    intro z hz
    exact hX i ⟨z, hz⟩
  have hspan (i : Fin k) : p.rep ∈
      Submodule.span ℂ (Set.range (fun z : s i => (z : ℙ ℂ W).rep)) := by
    have hbase := tensor_factor_mem_span p.rep p.rep_nonzero L b
      (fun l i => (q l i).rep) h i
    apply Submodule.span_mono ?_ hbase
    rintro _ ⟨l, rfl⟩
    exact ⟨⟨q l i, hmem l i⟩, rfl⟩
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan i)
  have hsupp (i : Fin k) : r ≤ (Finset.univ.filter (fun j => a i j ≠ 0)).card :=
    projective_expansion_support X p r hmin (fun z : s i => z) (hX i) (a i) (ha i).symm
  have hcount := tensor_product_support_bound
    (fun i (z : s i) => (z : ℙ ℂ W).rep) hli (fun _ => p.rep) a
    (fun i => (ha i).symm) L b (fun l i => ⟨q l i, hmem l i⟩) h
  calc
    r ^ k = ∏ _i : Fin k, r := by simp
    _ ≤ ∏ i : Fin k, (Finset.univ.filter (fun j => a i j ≠ 0)).card :=
      Finset.prod_le_prod' (fun i _ => hsupp i)
    _ ≤ L := hcount

#print axioms projective_tensor_decomposition_lower
end NLA.TR27.Paper
