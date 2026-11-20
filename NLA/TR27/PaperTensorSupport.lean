module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct Classical
namespace NLA.TR27.Paper

variable {ι : Type*} [Fintype ι]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Product of arbitrary dual coordinates on the actual iterated tensor product. -/
def tensorDual (f : ι → W →ₗ[ℂ] ℂ) :
    (⨂[ℂ] _ : ι, W) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f)

theorem tensorDual_tprod (f : ι → W →ₗ[ℂ] ℂ) (v : ι → W) :
    tensorDual f (PiTensorProduct.tprod ℂ v) = ∏ i, f i (v i) := by
  simp [tensorDual]

theorem independent_coordinate {κ : Type*} (x : κ → W) (hx : LinearIndependent ℂ x)
    (j : κ) : ∃ f : W →ₗ[ℂ] ℂ, ∀ l, f (x l) = if l = j then 1 else 0 := by
  classical
  let l : Submodule.span ℂ (Set.range x) →ₗ[ℂ] ℂ := (Finsupp.lapply j).comp hx.repr
  obtain ⟨f, hf⟩ := l.exists_extend
  refine ⟨f, ?_⟩
  intro k
  let v : Submodule.span ℂ (Set.range x) := ⟨x k, Submodule.subset_span ⟨k, rfl⟩⟩
  have heq := congrArg (fun g : Submodule.span ℂ (Set.range x) →ₗ[ℂ] ℂ => g v) hf
  change f (x k) = (hx.repr v) j at heq
  rw [heq, hx.repr_eq_single k v rfl]
  simp [Finsupp.single_apply]

/-- A sum of L pure coordinate tensors cannot have more than L nonzero
product coordinates. The families in different factors may be unrelated. -/
theorem tensor_product_support_bound {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (x : ∀ i, κ i → W) (hx : ∀ i, LinearIndependent ℂ (x i))
    (v : ι → W) (a : ∀ i, κ i → ℂ)
    (hv : ∀ i, v i = ∑ j, a i j • x i j)
    (L : ℕ) (b : Fin L → ℂ) (t : Fin L → ∀ i, κ i)
    (h : PiTensorProduct.tprod ℂ v =
      ∑ l, b l • PiTensorProduct.tprod ℂ (fun i => x i (t l i))) :
    (∏ i, (Finset.univ.filter (fun j => a i j ≠ 0)).card) ≤ L := by
  classical
  choose f hf using fun i j => independent_coordinate (x i) (hx i) j
  have hfv (i : ι) (j : κ i) : f i j (v i) = a i j := by
    rw [hv i, map_sum]
    simp [map_smul, hf, smul_eq_mul, mul_ite]
  let supports : ∀ i, Finset (κ i) := fun i => Finset.univ.filter (fun j => a i j ≠ 0)
  let tuples : Finset (∀ i, κ i) := Finset.univ.image t
  have hsub : Fintype.piFinset supports ⊆ tuples := by
    intro p hp
    have hprod : (∏ i, a i (p i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ =>
        (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2)
    by_contra hnot
    have hzero : tensorDual (fun i => f i (p i)) (PiTensorProduct.tprod ℂ v) = 0 := by
      rw [h, map_sum]
      apply Finset.sum_eq_zero
      intro l _
      rw [map_smul, tensorDual_tprod]
      have hneq : t l ≠ p := by
        intro heq
        exact hnot (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, heq⟩)
      obtain ⟨i, hi⟩ : ∃ i, t l i ≠ p i := by
        by_contra hn
        apply hneq
        funext i
        exact Classical.not_not.mp (fun hni => hn ⟨i, hni⟩)
      have hz : (∏ j, f j (p j) (x j (t l j))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hf, hi]
      rw [hz, smul_zero]
    rw [tensorDual_tprod] at hzero
    simp only [hfv] at hzero
    exact hprod hzero
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hcard
  exact hcard.trans (Finset.card_image_le.trans (by simp))

#print axioms tensor_product_support_bound

/-- Contracting a pure power shows that every factor belongs to the span
of the vectors used in that factor of any proposed tensor decomposition. -/
theorem tensor_factor_mem_span (v : W) (hv : v ≠ 0) (L : ℕ)
    (b : Fin L → ℂ) (x : Fin L → ι → W)
    (h : PiTensorProduct.tprod ℂ (fun _ : ι => v) =
      ∑ l, b l • PiTensorProduct.tprod ℂ (x l)) (i₀ : ι) :
    v ∈ Submodule.span ℂ (Set.range (fun l => x l i₀)) := by
  classical
  let S : Submodule ℂ W := Submodule.span ℂ (Set.range (fun l => x l i₀))
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S v).mp
  intro f hf
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  let F : ι → W →ₗ[ℂ] ℂ := Function.update (fun _ => g) i₀ f
  have hleft : tensorDual F (PiTensorProduct.tprod ℂ (fun _ : ι => v)) = f v := by
    rw [tensorDual_tprod]
    have heq : (fun i => F i v) = Function.update (fun _ => (1 : ℂ)) i₀ (f v) := by
      funext i
      by_cases hi : i = i₀ <;> simp [F, hi, hg]
    rw [heq]
    rw [Finset.prod_update_of_mem (Finset.mem_univ i₀)]
    simp
  have hright (l : Fin L) : tensorDual F (PiTensorProduct.tprod ℂ (x l)) = 0 := by
    rw [tensorDual_tprod]
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    have hz : f (x l i₀) = 0 :=
      (Submodule.mem_dualAnnihilator f).mp hf _ (Submodule.subset_span ⟨l, rfl⟩)
    simpa [F] using hz
  have hc := congrArg (tensorDual F) h
  simpa only [hleft, map_sum, map_smul, hright, smul_zero, Finset.sum_const_zero] using hc

#print axioms tensor_factor_mem_span
end NLA.TR27.Paper
