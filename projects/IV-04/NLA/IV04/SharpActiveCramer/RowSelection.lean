module

/- Select an actual square nonsingular original-row submatrix from a full Gram system. -/
public import NLA.IV04.OriginalObjectiveAttainment.IntegerAttainment
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04SharpActiveCramer
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem span_rows_eq_top_of_gram_det_ne_zero
    {ι : Type*} [Fintype ι] {n : ℕ} (M : Matrix ι (Fin n) ℚ)
    (hdet : (Mᵀ*M).det ≠ 0) : Submodule.span ℚ (Set.range M.row)=⊤ := by
  apply top_unique
  intro x hx
  let q := cramerCandidate (Mᵀ*M) x
  let w := M *ᵥ q
  have hs : (Mᵀ*M) *ᵥ q=x := cramerCandidate_solution _ _ hdet
  have heq : x=∑ i, w i • M.row i := by
    calc
      x = (Mᵀ*M) *ᵥ q := hs.symm
      _ = Mᵀ *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = _ := by
        funext j
        simp [Matrix.mulVec,dotProduct,Matrix.row,Finset.sum_apply,mul_comm]
  rw [heq]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

theorem exists_nonsingular_selected_rows
    {ι : Type*} [Fintype ι] {n : ℕ} (M : Matrix ι (Fin n) ℚ)
    (hdet : (Mᵀ*M).det ≠ 0) :
    ∃ f : Fin n → ι, Function.Injective f ∧ (M.submatrix f id).det ≠ 0 := by
  classical
  let R := Set.range M.row
  have hspan : ⊤ ≤ Submodule.span ℚ R := le_of_eq
    (span_rows_eq_top_of_gram_det_ne_zero M hdet).symm
  let J : Set (Fin n → ℚ) := (linearIndepOn_empty ℚ id).extend (Set.empty_subset R)
  have hJ : J ⊆ R := (linearIndepOn_empty ℚ id).extend_subset (Set.empty_subset R)
  let : Fintype J := ((Set.finite_range M.row).subset hJ).fintype
  let b : Module.Basis J ℚ (Fin n → ℚ) := Module.Basis.ofSpan hspan
  have hb (j : J) : b j=j.val := Module.Basis.ofSpan_apply_self hspan j
  have hcard : Fintype.card J=n := by
    have hc := Module.finrank_eq_card_basis b
    simpa using hc.symm
  let e : J ≃ Fin n := (Fintype.equivFin J).trans (finCongr hcard)
  let bF := b.reindex e
  have hrow (j : Fin n) : ∃ i, M.row i=bF j := by
    have hj : bF j ∈ R := by
      simp only [bF,Module.Basis.reindex_apply]
      rw [hb]
      exact hJ (e.symm j).property
    exact hj
  choose f hf using hrow
  have hli : LinearIndependent ℚ (fun j => M.row (f j)) := by
    have heq : (fun j => M.row (f j))=(fun j => bF j) := funext hf
    rw [heq]
    exact bF.linearIndependent
  have hinj : Function.Injective f := by
    intro i j hij
    apply hli.injective
    change M.row (f i)=M.row (f j)
    rw [hij]
  have hu : IsUnit (M.submatrix f id) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hli
  exact ⟨f,hinj,isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)⟩

#print axioms span_rows_eq_top_of_gram_det_ne_zero
#print axioms exists_nonsingular_selected_rows
end
end Reference.IV04SharpActiveCramer
