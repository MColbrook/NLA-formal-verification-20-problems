module

public import NLA.IV04.PaperCubeDefinitions
public import NLA.IV04.PaperVertices

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper

theorem determinant_entry_interpolation (n : ℕ) (A : Mat n) (i j : Fin n) (t : ℝ) :
    (Matrix.updateRow A i (Function.update (A i) j t)).det=
      ((1-t)/2)*(Matrix.updateRow A i (Function.update (A i) j (-1))).det+
        ((1+t)/2)*(Matrix.updateRow A i (Function.update (A i) j 1)).det := by
  have hr : Function.update (A i) j t=
      ((1-t)/2) • Function.update (A i) j (-1)+
        ((1+t)/2) • Function.update (A i) j 1 := by
    ext k
    by_cases hk : k=j <;> simp [Function.update_apply,hk,Pi.smul_apply,smul_eq_mul] <;> ring
  rw [hr,Matrix.det_updateRow_add,Matrix.det_updateRow_smul,Matrix.det_updateRow_smul]

namespace IntegerPartition

theorem uncertain_entries_distinct (P : IntegerPartition) (k l : Fin (P.m-1))
    (he : P.uncertainRow k=P.uncertainRow l) : k=l := by
  have h := congrArg Fin.val he
  dsimp [uncertainRow] at h
  apply Fin.ext
  omega

theorem uncertain_entry_value (P : IntegerPartition) (q : ℕ → ℝ) (k : Fin (P.m-1)) :
    P.layerMatrix q (P.uncertainRow k) (P.uncertainColumn k)=q k.val := by
  have hne : P.uncertainRow k ≠ P.uncertainColumn k := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [uncertainRow,uncertainColumn] at hv
    omega
  have hmod : (4*k.val+2)%4=2 := by omega
  have hdiv : (4*k.val+2)/4=k.val := by omega
  simp [layerMatrix,continuantMatrix,uncertainRow,uncertainColumn,hne,layerBeta,hmod,hdiv]

theorem layerMatrix_update_parameter (P : IntegerPartition) (q : ℕ → ℝ)
    (k : Fin (P.m-1)) (t : ℝ) :
    P.layerMatrix (Function.update q k.val t)=
      Matrix.updateRow (P.layerMatrix q) (P.uncertainRow k)
        (Function.update (P.layerMatrix q (P.uncertainRow k)) (P.uncertainColumn k) t) := by
  ext i j
  by_cases hi : i=P.uncertainRow k
  · subst i
    by_cases hj : j=P.uncertainColumn k
    · subst j
      simp [uncertain_entry_value]
    · have hival : (P.uncertainRow k).val=4*k.val+2 := rfl
      have hjval : j.val ≠ 4*k.val+1 := by
        intro h
        apply hj
        exact Fin.ext h
      simp only [Matrix.updateRow_apply,Function.update_self,Function.update_of_ne hj]
      dsimp [layerMatrix,continuantMatrix]
      split_ifs with hd hu hl
      · rfl
      · rfl
      · have := j.isLt
        simp only [uncertainRow] at hl
        omega
      · rfl
  · simp only [Matrix.updateRow_apply,Function.update_of_ne hi]
    dsimp [layerMatrix,continuantMatrix]
    split_ifs with hd hu hl
    · rfl
    · rfl
    · dsimp [layerBeta]
      split_ifs with h0 h1 h2
      · rfl
      · rfl
      · have hdiv : i.val/4 ≠ k.val := by
          intro hd
          apply hi
          apply Fin.ext
          dsimp [uncertainRow]
          omega
        exact Function.update_of_ne hdiv _ _
      · rfl
    · rfl

theorem determinant_parameter_interpolation (P : IntegerPartition) (q : ℕ → ℝ)
    (k : Fin (P.m-1)) (t : ℝ) :
    (P.layerMatrix (Function.update q k.val t)).det=
      ((1-t)/2)*(P.layerMatrix (Function.update q k.val (-1))).det+
        ((1+t)/2)*(P.layerMatrix (Function.update q k.val 1)).det := by
  simp only [layerMatrix_update_parameter]
  exact determinant_entry_interpolation _ _ _ _ _

end IntegerPartition
end IV04.Paper
