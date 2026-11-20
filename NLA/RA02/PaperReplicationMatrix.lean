module

public import NLA.RA02.PaperReplicationIsometry

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem rowReplication_mul_entry {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) (a : ReplicatedRows m) (j : Fin n) :
    (rowReplication m w*A) a j = (w a.1 : ℂ)*A a.1 j := by
  rw [Matrix.mul_apply,Finset.sum_eq_single a.1]
  · simp [rowReplication]
  · intro k _ hki
    simp [rowReplication,Ne.symm hki]
  · simp

theorem replicatedMatrix_entry {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) (a b : ReplicatedRows m) :
    replicatedMatrix m w A a b = (w a.1 : ℂ)*A a.1 b.1*(w b.1 : ℂ) := by
  rw [replicatedMatrix,Matrix.mul_apply,Finset.sum_eq_single b.1]
  · rw [rowReplication_mul_entry]
    simp [rowReplication,Matrix.conjTranspose_apply]
  · intro k _ hki
    simp [rowReplication,Matrix.conjTranspose_apply,Ne.symm hki]
  · simp

theorem replicatedMatrix_posSemidef {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) : (replicatedMatrix m w A).PosSemidef :=
  hA.mul_mul_conjTranspose_same (rowReplication m w)

theorem replicatedMatrix_trace {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n) :
    (replicatedMatrix m w A).trace = A.trace := by
  rw [replicatedMatrix,Matrix.trace_mul_cycle,rowReplication_isometry m w hw,Matrix.one_mul]

theorem replicatedMatrix_gram_trace {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n) :
    ((replicatedMatrix m w A).conjTranspose*replicatedMatrix m w A).trace =
      (A.conjTranspose*A).trace := by
  let P := rowReplication m w
  have hP : P.conjTranspose*P=1 := rowReplication_isometry m w hw
  have hg : (replicatedMatrix m w A).conjTranspose*replicatedMatrix m w A =
      P*(A.conjTranspose*A)*P.conjTranspose := by
    dsimp [replicatedMatrix]
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _ = P*A.conjTranspose*(P.conjTranspose*P)*A*P.conjTranspose := by
        simp only [Matrix.mul_assoc,P]
      _ = _ := by rw [hP,Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [hg,Matrix.trace_mul_cycle,hP,Matrix.one_mul]

#print axioms replicatedMatrix_gram_trace
end NLA.RA02.Paper
