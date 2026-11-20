module

public import NLA.PF02.PositiveBasis.Independent

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02PositiveBasis
open Matrix NLA.PF02.Paper
open scoped BigOperators MatrixOrder

theorem trace_gram_rank_of_linearIndependent {ι : Type*} [Fintype ι] {n : ℕ}
    (F : ι → Matrix (Fin n) (Fin n) ℝ) (hF : ∀ i, (F i).transpose = F i)
    (hlin : LinearIndependent ℝ F) : (traceGram F).rank = Fintype.card ι := by
  classical
  let V : Matrix ι (Fin n × Fin n) ℝ := fun p ij => F p ij.1 ij.2
  have hV : LinearIndependent ℝ V.row := by
    rw [Fintype.linearIndependent_iff]
    intro c hz i
    apply (Fintype.linearIndependent_iff.mp hlin c) _ i
    ext u v
    have h := congrFun hz (u,v)
    simpa [V, Matrix.row, Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply] using h
  have he : traceGram F = V * V.transpose := by
    ext p q
    change (∑ i, ∑ j, F p i j * F q j i) = ∑ a : Fin n × Fin n, F p a.1 a.2 * F q a.1 a.2
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun x : ℝ => F p i j * x) (congrFun (congrFun (hF q) i) j)
  rw [he, Matrix.rank_self_mul_transpose]
  exact hV.rank_matrix

theorem positive_gram_rank (n : ℕ) : (positiveGram n).rank = n * (n+1) / 2 := by
  change (traceGram (positiveMatrix (n := n))).rank = _
  rw [trace_gram_rank_of_linearIndependent _ positive_matrix_symmetric
    (positive_matrices_linearIndependent n), symmetricIndex_card]

#print axioms trace_gram_rank_of_linearIndependent
#print axioms positive_gram_rank
end Reference.PF02PositiveBasis
