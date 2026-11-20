module

public import NLA.NM04.Canonical
public import NLA.NM04.PaperDerivatives
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.NM04.Paper
universe u v
attribute [local instance] Classical.propDecidable

-- Fix the scalar-continuity witness in both independent environments.
attribute [local instance] ContinuousMul.to_continuousSMul
attribute [-instance] IsModuleTopology.toContinuousSMul

theorem paper_rowland_wu_identity {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) :
    (∑ E : Finset (Index m n),
      ((m : ℝ)⁻¹ • (HReal m n).submatrix
        (Subtype.val : E → Index m n) (Subtype.val : E → Index m n)).det *
      (∏ I ∈ E, delta A hm hn I) * (∏ I ∈ (Finset.univ \ E), gamma A hm hn I) *
      ((sinkhorn A) (firstIndex hm) (firstIndex hn)) ^ E.card) = 0 := by
  exact rowland_wu_identity hm hn A hA

theorem paper_minor_derivatives {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
    (T : Matrix α β ℝ) (I : MinorIndex α β) :
    HasDerivAt (fun z : ℝ => minor
      (T + z • Matrix.of (fun (_ : α) (_ : β) => (1 : ℝ))) I)
      (lowering (minor T) I) 0 ∧
    HasDerivAt (fun z : ℝ => minor
      (T + z • Matrix.vecMulVec (fun i => ∑ j, T i j) (fun _ => (1 : ℝ))) I)
      ((I.1.1.card : ℝ) * minor T I + columnExchange (minor T) I) 0 ∧
    HasDerivAt (fun z : ℝ => minor
      (T + z • Matrix.vecMulVec (fun _ => (1 : ℝ)) (fun j => ∑ i, T i j)) I)
      ((I.1.1.card : ℝ) * minor T I + rowExchange (minor T) I) 0 ∧
    HasDerivAt (fun z : ℝ => minor
      (T + z • Matrix.vecMulVec (fun i => ∑ j, T i j) (fun j => ∑ i, T i j)) I)
      ((∑ i, ∑ j, T i j) * minor T I - raising (minor T) I) 0 := by
  exact minor_directional_derivatives T I

#print axioms paper_rowland_wu_identity
#print axioms paper_minor_derivatives

end NLA.NM04.Paper
