module

public import NLA.NM04.RankOneBordered
public import NLA.NM04.MinorLowering
public import NLA.NM04.MinorColumnExchange
public import NLA.NM04.MinorRowExchange
public import NLA.NM04.MinorRaising
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.NM04.Paper
universe u v
attribute [local instance] Classical.propDecidable

theorem rank_one_minor_derivative {α : Type u} {β : Type v}
    [LinearOrder α] [LinearOrder β] (T : Matrix α β ℝ)
    (a : α → ℝ) (b : β → ℝ) (I : MinorIndex α β) :
    HasDerivAt (fun z : ℝ => minor (T + z • Matrix.vecMulVec a b) I)
      (cofactorForm T I (Matrix.vecMulVec a b)) 0 := by
  simp_rw [universal_rank_one_update]
  exact (hasDerivAt_mul_const (x := (0 : ℝ))
    (cofactorForm T I (Matrix.vecMulVec a b))).const_add (minor T I)

theorem minor_directional_derivatives {α : Type u} {β : Type v}
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := rank_one_minor_derivative T (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) I
    have he : Matrix.vecMulVec (fun _ : α => (1 : ℝ)) (fun _ : β => (1 : ℝ)) =
        (fun _ _ => (1 : ℝ)) := by ext; simp [Matrix.vecMulVec]
    rw [he, minor_lowering_identity] at h
    exact h
  · simpa only [minor_column_exchange_identity] using
      rank_one_minor_derivative T (fun i => ∑ j, T i j) (fun _ => (1 : ℝ)) I
  · simpa only [minor_row_exchange_identity] using
      rank_one_minor_derivative T (fun _ => (1 : ℝ)) (fun j => ∑ i, T i j) I
  · simpa only [minor_raising_identity] using
      rank_one_minor_derivative T (fun i => ∑ j, T i j) (fun j => ∑ i, T i j) I

#print axioms minor_directional_derivatives
end NLA.NM04.Paper
