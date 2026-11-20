module

public import NLA.NM04.PositiveMargins.Definitions
public import NLA.NM04.MinorColumnExchange
public import NLA.NM04.MinorTranspose
public import NLA.NM04.MinorRaising
public import Mathlib.Tactic
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace NLA.NM04.PositiveMargins
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v
variable {α : Type u} {β : Type v}
variable [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]

theorem weighted_lower (T : Matrix α β ℝ) (I : MinorIndex α β)
    (a : α → ℝ) (b : β → ℝ) :
    cofactorForm T I (Matrix.vecMulVec a b) = lower a b (minor T) I := by
  exact cofactor_signed_minor_formula T (Matrix.vecMulVec a b) I

theorem weighted_column_sum (T : Matrix α β ℝ) (I : MinorIndex α β) (b : β → ℝ) :
    cofactorForm T I (Matrix.vecMulVec (fun r => ∑ t, T r t) b) =
      ∑ s : I.1.2, b s * ∑ t : β, columnForm T I s (fun r => T r t) := by
  let A := minorMatrix T I
  let e := I.1.2.orderIsoOfFin I.property.symm
  calc
    _ = ∑ j : Fin I.1.1.card, b (e j) *
        ∑ t : β, ∑ i : Fin I.1.1.card,
          A.adjugate j i * T (I.1.1.orderEmbOfFin rfl i) t := by
      change (∑ i : Fin I.1.1.card, ∑ j : Fin I.1.1.card,
          A.adjugate j i * ((∑ t : β, T (I.1.1.orderEmbOfFin rfl i) t) *
            b (I.1.2.orderEmbOfFin I.property.symm j))) = _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∑ i : Fin I.1.1.card, ∑ t : β,
            b (e j) * (A.adjugate j i * T (I.1.1.orderEmbOfFin rfl i) t) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro t _
          change A.adjugate j i * (T (I.1.1.orderEmbOfFin rfl i) t * b (e j)) =
            b (e j) * (A.adjugate j i * T (I.1.1.orderEmbOfFin rfl i) t)
          ring
        _ = ∑ t : β, ∑ i : Fin I.1.1.card,
            b (e j) * (A.adjugate j i * T (I.1.1.orderEmbOfFin rfl i) t) :=
          Finset.sum_comm
        _ = _ := by simp only [Finset.mul_sum]
    _ = _ := by
      refine Fintype.sum_equiv e.toEquiv _ _ ?_
      intro j
      apply congrArg (fun z : ℝ => b (e j) * z)
      apply Finset.sum_congr rfl
      intro t _
      calc
        _ = ∑ i : Fin I.1.1.card, A.adjugate (e.symm (e j)) i *
            T (I.1.1.orderEmbOfFin rfl i) t :=
          congrArg (fun l : Fin I.1.1.card => ∑ i : Fin I.1.1.card,
            A.adjugate l i * T (I.1.1.orderEmbOfFin rfl i) t) (e.symm_apply_apply j).symm
        _ = _ := (minorColumnForm_adjugate T I (e j) (fun r => T r t)).symm

theorem weighted_column (T : Matrix α β ℝ) (I : MinorIndex α β) (b : β → ℝ) :
    cofactorForm T I (Matrix.vecMulVec (fun r => ∑ t, T r t) b) =
      (∑ s : I.1.2, b s) * minor T I + column b (minor T) I := by
  have hselected (s : I.1.2) :
      (∑ d : I.1.2, minorColumnForm T I s (fun r => T r d)) = minor T I := by
    calc
      _ = ∑ d : I.1.2, if d = s then minor T I else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        exact minorColumnForm_selected T I s d
      _ = _ := by simp
  have huniv : @Finset.univ I.1.2 (Subtype.fintype (fun t : β => t ∈ I.1.2)) =
      @Finset.univ I.1.2 (Finset.Subtype.fintype I.1.2) :=
    congrArg (fun d : Fintype I.1.2 => @Finset.univ I.1.2 d) (Subsingleton.elim _ _)
  calc
    _ = ∑ s : I.1.2, b s * ∑ t : β, minorColumnForm T I s (fun r => T r t) :=
      weighted_column_sum T I b
    _ = ∑ s : I.1.2, b s * (minor T I +
        ∑ t : {t : β // t ∉ I.1.2},
          (-1 : ℝ) ^ (position (s : β) I.1.2 + position (t : β) (exchangeColumn I s t).1.2) *
            minor T (exchangeColumn I s t)) := by
      apply Finset.sum_congr rfl
      intro s _
      apply congrArg (fun z : ℝ => b s * z)
      calc
        _ = (∑ d : I.1.2, minorColumnForm T I s (fun r => T r d)) +
            ∑ t : {t : β // t ∉ I.1.2}, minorColumnForm T I s (fun r => T r t) := by
          simpa only [huniv] using
            (Fintype.sum_subtype_add_sum_subtype (fun t : β => t ∈ I.1.2)
              (fun t => minorColumnForm T I s (fun r => T r t))).symm
        _ = _ := congrArg₂ (· + ·) (hselected s) (Finset.sum_congr rfl
          (fun t _ => minorColumnForm_exchange T I s t))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
        column, mul_assoc]

theorem weighted_row (T : Matrix α β ℝ) (I : MinorIndex α β) (a : α → ℝ) :
    cofactorForm T I (Matrix.vecMulVec a (fun j => ∑ i, T i j)) =
      (∑ s : I.1.1, a s) * minor T I + row a (minor T) I := by
  let Z := Matrix.vecMulVec a (fun j => ∑ i, T i j)
  have hZ : Matrix.vecMulVec (fun j => ∑ i, Tᵀ j i) a = Zᵀ := by
    ext j i
    simp only [Z, Matrix.vecMulVec_apply, Matrix.transpose_apply]
    ring
  calc
    _ = cofactorForm Tᵀ (minorTransposeIndex I) Zᵀ := (cofactorForm_transpose T I Z).symm
    _ = cofactorForm Tᵀ (minorTransposeIndex I)
        (Matrix.vecMulVec (fun j => ∑ i, Tᵀ j i) a) :=
      congrArg (cofactorForm Tᵀ (minorTransposeIndex I)) hZ.symm
    _ = (∑ s : I.1.1, a s) * minor Tᵀ (minorTransposeIndex I) +
        column a (minor Tᵀ) (minorTransposeIndex I) := weighted_column Tᵀ (minorTransposeIndex I) a
    _ = _ := by
      rw [minor_transpose]
      apply congrArg (fun z : ℝ => (∑ s : I.1.1, a s) * minor T I + z)
      unfold column row
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      have hm : minor Tᵀ (exchangeColumn (minorTransposeIndex I) s t) =
          minor T (exchangeRow I s t) :=
        minor_transpose T (exchangeRow I s t)
      rw [hm]
      rfl

theorem weighted_direction (T : Matrix α β ℝ) (I : MinorIndex α β)
    (a : α → ℝ) (b : β → ℝ) :
    cofactorForm T I (Matrix.vecMulVec
      (fun i => a i - ∑ j, T i j) (fun j => b j - ∑ i, T i j)) =
      lower a b (minor T) I -
        ((∑ s : I.1.2, b s) * minor T I + column b (minor T) I) -
        ((∑ s : I.1.1, a s) * minor T I + row a (minor T) I) +
        (∑ i, ∑ j, T i j) * minor T I - raising (minor T) I := by
  have hdir : Matrix.vecMulVec
      (fun i => a i - ∑ j, T i j) (fun j => b j - ∑ i, T i j) =
      Matrix.vecMulVec a b +
        (-1 : ℝ) • Matrix.vecMulVec (fun i => ∑ j, T i j) b +
        (-1 : ℝ) • Matrix.vecMulVec a (fun j => ∑ i, T i j) +
        Matrix.vecMulVec (fun i => ∑ j, T i j) (fun j => ∑ i, T i j) := by
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hdir]
  simp only [cofactorForm_add, cofactorForm_smul]
  rw [weighted_column, weighted_row, weighted_lower, minor_raising_identity]
  ring

#print axioms weighted_lower
#print axioms weighted_column_sum
#print axioms weighted_column
#print axioms weighted_row
#print axioms weighted_direction
end
end NLA.NM04.PositiveMargins
