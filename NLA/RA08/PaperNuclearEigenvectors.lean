module

public import NLA.RA08.PaperNuclearDifference
public import NLA.RA08.PaperNuclearSine
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearShift_mulVec {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    (nuclearShift m *ᵥ x) i = if hi : 0 < i.val then x ⟨i.val-1,by omega⟩ else 0 := by
  have h := nuclearShift_mul (fun k (_ : Fin 1) => x k) i 0
  simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct] using h

theorem nuclearShift_transpose_mulVec {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    ((nuclearShift m).transpose *ᵥ x) i =
      if hi : i.val+1<m then x ⟨i.val+1,hi⟩ else 0 := by
  simp only [Matrix.mulVec,dotProduct]
  by_cases hi : i.val+1<m
  · rw [dif_pos hi]
    let k : Fin m := ⟨i.val+1,hi⟩
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.transpose_apply,nuclearShift,show k.val=i.val+1 from rfl,
        ite_true,one_mul]
      rfl
    · intro b _ hbk
      have hb : b.val ≠ i.val+1 := fun h => hbk (Fin.ext h)
      simp [Matrix.transpose_apply,nuclearShift,hb]
    · simp
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro b _
    have hb : b.val ≠ i.val+1 := by omega
    simp [Matrix.transpose_apply,nuclearShift,hb]

theorem nuclearDifference_gram_action {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    (((nuclearDifference m).transpose*nuclearDifference m) *ᵥ x) i =
      x i-(if hi : 0 < i.val then x ⟨i.val-1,by omega⟩ else 0)-
      (if hi : i.val+1<m then x ⟨i.val+1,hi⟩ else 0)+
      (if i.val+1<m then (1 : ℝ) else 0)*x i := by
  rw [nuclearDifference_gram,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.sub_mulVec,
    Matrix.one_mulVec]
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [nuclearShift_mulVec,nuclearShift_transpose_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

theorem nuclearSineVector_eigenvector {m : ℕ} (j : Fin m) :
    ((nuclearDifference m).transpose*nuclearDifference m) *ᵥ nuclearSineVector j =
      nuclearDifferenceEigenvalue j • nuclearSineVector j := by
  ext i
  rw [nuclearDifference_gram_action]
  simp only [Pi.smul_apply,smul_eq_mul,nuclearSineVector,nuclearDifferenceEigenvalue]
  have hp : (if hi : 0 < i.val then
      Real.sin (((i.val-1+1 : ℕ) : ℝ)*nuclearSineAngle j) else 0) =
      Real.sin ((i.val : ℝ)*nuclearSineAngle j) := by
    split_ifs with hi
    · rw [show i.val-1+1=i.val by omega]
    · have hz : i.val=0 := by omega
      simp [hz]
  rw [hp]
  have hr := nuclear_sine_recurrence (((i.val+1 : ℕ) : ℝ)*nuclearSineAngle j)
    (nuclearSineAngle j)
  rw [show ((i.val+1 : ℕ) : ℝ)*nuclearSineAngle j-nuclearSineAngle j =
      (i.val : ℝ)*nuclearSineAngle j by push_cast; ring,
    show ((i.val+1 : ℕ) : ℝ)*nuclearSineAngle j+nuclearSineAngle j =
      ((i.val+2 : ℕ) : ℝ)*nuclearSineAngle j by push_cast; ring] at hr
  by_cases hi : i.val+1<m
  · rw [dif_pos hi,if_pos hi]
    have hn : i.val+1+1=i.val+2 := by omega
    rw [hn]
    linarith
  · rw [dif_neg hi,if_neg hi]
    have hilast : i.val+1=m := by omega
    have hnext : i.val+2=m+1 := by omega
    rw [hnext,hilast,nuclearSineAngle_boundary] at hr
    rw [hilast]
    linarith

#print axioms nuclearSineVector_eigenvector

theorem nuclearSineVector_linearIndependent (m : ℕ) :
    LinearIndependent ℝ (nuclearSineVector (m := m)) := by
  let G : Module.End ℝ (Fin m → ℝ) :=
    ((nuclearDifference m).transpose*nuclearDifference m).mulVecLin
  apply G.eigenvectors_linearIndependent' nuclearDifferenceEigenvalue
    (nuclearDifferenceEigenvalue_injective m) nuclearSineVector
  intro j
  exact ⟨Module.End.mem_eigenspace_iff.mpr (nuclearSineVector_eigenvector j),
    nuclearSineVector_ne_zero j⟩

noncomputable def nuclearSineBasis (m : ℕ) : Module.Basis (Fin m) ℝ (Fin m → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' nuclearSineVector
    (nuclearSineVector_linearIndependent m) (by simp [Module.finrank_pi])

theorem nuclearSineBasis_apply (m : ℕ) (j : Fin m) :
    nuclearSineBasis m j=nuclearSineVector j := by
  unfold nuclearSineBasis
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) _ _ _) j

theorem nuclearSineVector_span (m : ℕ) :
    Submodule.span ℝ (Set.range (nuclearSineVector (m := m)))=⊤ := by
  exact (nuclearSineVector_linearIndependent m).span_eq_top_of_card_eq_finrank'
    (by simp [Module.finrank_pi])

#print axioms nuclearSineVector_span
end NLA.RA08.Paper
