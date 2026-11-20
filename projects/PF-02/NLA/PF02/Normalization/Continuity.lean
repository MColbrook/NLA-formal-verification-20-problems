module

public import NLA.PF02.Normalization.Normalization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Topology.Instances.Matrix

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

theorem continuous_row_sum (p k : ℕ) :
    Continuous (rowSum : (Fin p → Mat (Fin k)) → Mat (Fin k)) := by
  unfold rowSum
  fun_prop

theorem continuousOn_root_sum (p k : ℕ) :
    ContinuousOn (rootSum : (Fin p → Mat (Fin k)) → Mat (Fin k))
      {A | (rowSum A).PosDef} := by
  apply CFC.continuousOn_sqrt.comp (continuous_row_sum p k).continuousOn
  exact fun A hA => hA.posSemidef.nonneg

theorem continuousOn_inverse_root_sum (p k : ℕ) :
    ContinuousOn (fun A : Fin p → Mat (Fin k) => (rootSum A)⁻¹)
      {A | (rowSum A).PosDef} := by
  intro A hA
  have hu := (Matrix.isUnit_iff_isUnit_det (rootSum A)).mp (root_sum_isUnit A hA)
  have hi : ContinuousAt (fun H : Mat (Fin k) => H⁻¹) (rootSum A) :=
    continuousAt_matrix_inv (rootSum A) (by
      have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext (fun x => Ring.inverse_eq_inv x)
      rw [heq]
      exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp hu))
  exact hi.comp_continuousWithinAt (continuousOn_root_sum p k A hA)

theorem continuousOn_normalized_row (p k : ℕ) (i : Fin p) :
    ContinuousOn (fun A : Fin p → Mat (Fin k) => normalizedRow A i)
      {A | (rowSum A).PosDef} :=
  ((continuousOn_inverse_root_sum p k).mul (continuous_apply i).continuousOn).mul
    (continuousOn_inverse_root_sum p k)

theorem continuousOn_normalized_column (p q k : ℕ) (j : Fin q) :
    ContinuousOn (fun F : (Fin p → Mat (Fin k)) × (Fin q → Mat (Fin k)) =>
      normalizedColumn F.1 F.2 j) {F | (rowSum F.1).PosDef} := by
  have hr : ContinuousOn (fun F : (Fin p → Mat (Fin k)) × (Fin q → Mat (Fin k)) =>
      rootSum F.1) {F | (rowSum F.1).PosDef} :=
    (continuousOn_root_sum p k).comp continuous_fst.continuousOn (fun F hF => hF)
  exact (hr.mul ((continuous_apply j).comp continuous_snd).continuousOn).mul hr

#print axioms continuous_row_sum
#print axioms continuousOn_root_sum
#print axioms continuousOn_inverse_root_sum
#print axioms continuousOn_normalized_row
#print axioms continuousOn_normalized_column
end Reference.PF02Normalization
