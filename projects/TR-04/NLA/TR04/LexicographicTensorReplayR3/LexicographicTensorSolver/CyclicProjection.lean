module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Actual spectral-mask frames, projectors and literal Frobenius energy. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.CyclicCombinatorics
public import NLA.TR04.OptimalityEquality.ProjectorRanks

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RealColumnCompression
open scoped BigOperators Matrix

theorem indicatorFrame_orthonormal {m : ℕ} (V : Square m) (hV : IsOrthogonal V)
    (p : Fin m → Prop) : (indicatorFrame V p).transpose*indicatorFrame V p=1 := by
  classical
  let f := fun j : Fin (Fintype.card {i : Fin m // p i}) =>
    ((Reference.LexOrderedIndex.indexEnum p).symm j).val
  have hf : Function.Injective f := Subtype.val_injective.comp (Reference.LexOrderedIndex.indexEnum p).symm.injective
  change (V.transpose*V).submatrix f f=1
  rw [hV.1]
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.one_apply,hf.eq_iff]

theorem indicatorFrame_projector {m : ℕ} (V : Square m) (p : Fin m → Prop) :
    indicatorFrame V p*(indicatorFrame V p).transpose=indicatorProjector V p := by
  classical
  let e := Reference.LexOrderedIndex.indexEnum p
  ext a b
  change (∑ j : Fin (Fintype.card {i : Fin m // p i}), V a (e.symm j).val*V b (e.symm j).val)=_
  rw [e.symm.sum_comp (fun i : {i : Fin m // p i} => V a i.val*V b i.val)]
  have hs := Finset.sum_subtype (p:=p) (F:=inferInstance) (Finset.univ.filter p) (by simp) (fun i : Fin m => V a i*V b i)
  rw [← hs]
  rw [indicatorProjector,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : p i <;> simp [indicator,hp]

theorem indicatorProjector_frobenius {m n : ℕ} (V : Square m) (hV : IsOrthogonal V)
    (p : Fin m → Prop) (R : Rect m n) :
    frobeniusSq (indicatorProjector V p*R)=
      ∑ i : Fin m, indicator p i*(∑ b : Fin n, (V.transpose*R) i b^2) := by
  classical
  rw [indicatorProjector,Matrix.mul_assoc,Matrix.mul_assoc,frobeniusSq_frame_mul V hV.1]
  unfold frobeniusSq
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : p i
  · simp [indicator,hp,Matrix.diagonal_mul]
  · simp [indicator,hp,Matrix.diagonal_mul]

theorem candidateProjector_split {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) :
    candidateProjector A tau s j=leftAboveProjector A tau+windowProjector A tau s j := by
  classical
  have hmask : indicator (selected A tau s j)=
      (fun i => if tau<singularValue A.transpose i.val then (1 : ℝ) else 0)+
        indicator (windowSelected A tau s j) := by
    funext i
    by_cases ha : tau<singularValue A.transpose i.val
    · have he : singularValue A.transpose i.val≠tau := ne_of_gt ha
      simp [indicator,selected,windowSelected,ha,he]
    · simp [indicator,selected,ha]
  simp only [candidateProjector,windowProjector,indicatorProjector,leftAboveProjector]
  rw [hmask]
  have hd : Matrix.diagonal ((fun i : Fin m => if tau<singularValue A.transpose i.val then (1 : ℝ) else 0)+indicator (windowSelected A tau s j))=
      Matrix.diagonal (fun i : Fin m => if tau<singularValue A.transpose i.val then (1 : ℝ) else 0)+Matrix.diagonal (indicator (windowSelected A tau s j)) := by
    ext a b
    by_cases h : a=b <;> simp [Pi.add_apply,h]
  rw [hd,Matrix.mul_add,Matrix.add_mul]

theorem actual_cyclic_projector_sum {m n : ℕ} (A : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau) :
    (∑ j : Fin (eCount A tau), windowProjector A tau s j)=
      (s : ℝ) • leftBoundaryProjector A tau := by
  classical
  have hdiag : (∑ j : Fin (eCount A tau), Matrix.diagonal (indicator (windowSelected A tau s j)))=
      (s : ℝ) • Matrix.diagonal (fun i : Fin m => if singularValue A.transpose i.val=tau then (1 : ℝ) else 0) := by
    ext a b
    by_cases hab : a=b
    · subst b
      simpa only [Matrix.sum_apply,Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul] using
        actual_window_column_sum A tau s hs a
    · simp [Matrix.sum_apply,hab]
  unfold windowProjector indicatorProjector leftBoundaryProjector
  rw [← Finset.sum_mul,← Finset.mul_sum,hdiag]
  simp only [Matrix.mul_smul,Matrix.smul_mul]

theorem actual_cyclic_projected_error_sum {m n : ℕ} (A R : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau) :
    (∑ j : Fin (eCount A tau), frobeniusSq (windowProjector A tau s j*R))=
      (s : ℝ)*frobeniusSq (leftBoundaryProjector A tau*R) := by
  classical
  have hV := leftVectorMatrix_orthogonal A
  simp only [windowProjector,indicatorProjector_frobenius _ hV]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,actual_window_column_sum A tau s hs]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have hb : leftBoundaryProjector A tau=indicatorProjector (leftVectorMatrix A)
      (fun i => singularValue A.transpose i.val=tau) := rfl
  rw [hb,indicatorProjector_frobenius _ hV]
  rfl

#print axioms indicatorFrame_orthonormal
#print axioms indicatorFrame_projector
#print axioms actual_cyclic_projector_sum
#print axioms actual_cyclic_projected_error_sum
end
end Reference.LexOrderedCyclicBoundary