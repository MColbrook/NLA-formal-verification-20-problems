module

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Actual finite window/cardinality/frame dimensions, without dimension or rank oracles. -/
public import NLA.TR04.LexicographicTensorSolver.CyclicProjection

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix BigOperators

theorem subtype_indicator_sum {m : ℕ} (p : Fin m → Prop) (f : Fin m → ℝ) :
    (∑ i : {i : Fin m // p i}, f i.val)=∑ i : Fin m, indicator p i*f i := by
  classical
  rw [← Finset.sum_subtype (p:=p) (F:=inferInstance) (Finset.univ.filter p) (by simp) f,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : p i <;> simp [indicator,hp]

theorem indicator_sum_eq_card {m : ℕ} (p : Fin m → Prop) :
    (∑ i : Fin m, indicator p i)=(Fintype.card {i : Fin m // p i} : ℝ) := by
  classical
  rw [Fintype.card_subtype]
  unfold indicator
  rw [← Finset.sum_filter]
  simp

theorem actual_window_row_sum {m n : ℕ} (A : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau) (j : Fin (eCount A tau)) :
    (∑ i : Fin m, indicator (windowSelected A tau s j) i)=(s : ℝ) := by
  classical
  let ep := fun i : Fin m => singularValue A.transpose i.val=tau
  have hrestrict : ∀ i : Fin m,
      indicator (windowSelected A tau s j) i=indicator ep i*indicator (windowSelected A tau s j) i := by
    intro i
    by_cases he : ep i
    · simp [indicator,he]
    · have he' : singularValue A.transpose i.val≠tau := he
      simp [indicator,ep,windowSelected,he']
  calc
    _ = ∑ i : Fin m, indicator ep i*indicator (windowSelected A tau s j) i :=
      Finset.sum_congr rfl (fun i hi => hrestrict i)
    _ = ∑ i : EIndex A tau, indicator (windowSelected A tau s j) i.val :=
      (subtype_indicator_sum ep _).symm
    _ = ∑ i : EIndex A tau, if inWindow s j (boundaryOrdinal A tau i) then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [indicator,windowSelected,dif_pos i.property]
      rfl
    _ = ∑ i : Fin (eCount A tau), if inWindow s j i then (1 : ℝ) else 0 :=
      (boundaryOrdinal A tau).sum_comp (fun i => if inWindow s j i then (1 : ℝ) else 0)
    _ = _ := cyclic_window_row_sum hs j

theorem window_card {m n : ℕ} (A : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau) (j : Fin (eCount A tau)) :
    Fintype.card {i : Fin m // windowSelected A tau s j i}=s := by
  exact Nat.cast_injective (R:=ℝ) ((indicator_sum_eq_card _).symm.trans
    (actual_window_row_sum A tau s hs j))

theorem selected_card {m n : ℕ} (A : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau) (j : Fin (eCount A tau)) :
    Fintype.card {i : Fin m // selected A tau s j i}=hCount A tau+s := by
  classical
  have hmask : ∀ i : Fin m, indicator (selected A tau s j) i=
      indicator (fun i => tau<singularValue A.transpose i.val) i+indicator (windowSelected A tau s j) i := by
    intro i
    by_cases ha : tau<singularValue A.transpose i.val
    · have he : singularValue A.transpose i.val≠tau := ne_of_gt ha
      simp [indicator,selected,windowSelected,ha,he]
    · simp [indicator,selected,ha]
  apply Nat.cast_injective (R:=ℝ)
  calc
    _ = ∑ i : Fin m, indicator (selected A tau s j) i := (indicator_sum_eq_card _).symm
    _ = _ := Finset.sum_congr rfl (fun i hi => hmask i)
    _ = _ := by rw [Finset.sum_add_distrib,indicator_sum_eq_card,actual_window_row_sum A tau s hs j,Nat.cast_add];rfl

theorem actual_boundary_parameters {m n : ℕ} (A : Rect m n) (r : ℕ)
    (hr : 0<r) (hrank : r<A.rank) :
    0<r-hCount A (singularValue A (r-1)) ∧
    r-hCount A (singularValue A (r-1)) ≤ eCount A (singularValue A (r-1)) ∧
    hCount A (singularValue A (r-1))+(r-hCount A (singularValue A (r-1)))=r := by
  classical
  have hrm : r<m := hrank.trans_le (Matrix.rank_le_height A)
  let tau := singularValue A (r-1)
  let E := Finset.univ.filter (fun i : Fin m => singularValue A.transpose i.val=tau)
  let S := E.filter (fun i => i.val<r)
  let i : Fin m := ⟨r-1,by omega⟩
  have hi : i ∈ S := by simp [S,E,i,tau,singularValue_transpose];omega
  have hpos : 0<S.card := Finset.card_pos.mpr ⟨i,hi⟩
  have hle : S.card ≤ E.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hid : S.card=r-hCount A tau := by
    rw [hCount_eq_aboveMultiplicity]
    exact retained_boundary_multiplicity_eq_rank_sub_above A r hr hrank
  have heq : E.card=eCount A tau := (eCount_eq_boundaryMultiplicity A tau).symm
  rw [hid] at hpos hle
  rw [heq] at hle
  dsimp [tau] at hpos hle
  exact ⟨hpos,hle,by omega⟩

theorem actual_candidate_frame {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) :
    (candidateFrame A tau s j).transpose*candidateFrame A tau s j=1 ∧
    candidateFrame A tau s j*(candidateFrame A tau s j).transpose=candidateProjector A tau s j := by
  exact ⟨indicatorFrame_orthonormal _ (leftVectorMatrix_orthogonal A) _,indicatorFrame_projector _ _⟩

#print axioms actual_window_row_sum
#print axioms selected_card
#print axioms actual_boundary_parameters
#print axioms actual_candidate_frame
end
end Reference.LexOrderedCyclicBoundary