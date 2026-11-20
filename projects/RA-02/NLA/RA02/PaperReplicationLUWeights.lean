module

public import NLA.RA02.PaperReplicationSums
public import NLA.RA02.PaperFrobeniusIsometry

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem finiteReplication_frobenius {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n) :
    NLA.RA03.frobeniusSq (finiteReplicatedMatrix m w A)=NLA.RA03.frobeniusSq A :=
  frobenius_isometric_embedding (finiteRowReplication m w) (finiteRowReplication_isometry m w hw) A

theorem finiteReplication_zero_iff {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n) :
    finiteReplicatedMatrix m w A=0 ↔ A=0 := by
  rw [← lu_frobeniusSq_eq_zero_iff,finiteReplication_frobenius m w hw,lu_frobeniusSq_eq_zero_iff]

theorem finiteReplication_entry_normSq {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) (a b : Fin (replicationDimension m)) :
    Complex.normSq (finiteReplicatedMatrix m w A a b)=
      (w ((replicationLabels m).symm a).1)^2*(w ((replicationLabels m).symm b).1)^2*
        Complex.normSq (A ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1) := by
  rw [finiteReplicatedMatrix_entry]
  simp only [Complex.normSq_mul,Complex.normSq_ofReal,pow_two]
  ring

theorem finiteReplication_lu_mass_sum {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n)
    (F : Fin n → Fin n → ℝ) :
    (∑ a : Fin (replicationDimension m), ∑ b : Fin (replicationDimension m),
      NLA.RA03.pivotMass (finiteReplicatedMatrix m w A) (some (a,b))*
        F ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1) =
      ∑ i, ∑ j, NLA.RA03.pivotMass A (some (i,j))*F i j := by
  by_cases hA : A=0
  · subst A
    have hz : finiteReplicatedMatrix m w (0 : NLA.RA02.Square n)=0 := (finiteReplication_zero_iff m w hw _).mpr rfl
    simp only [hz,NLA.RA03.pivotMass,ite_true,zero_mul,Finset.sum_const_zero]
  · have hC : finiteReplicatedMatrix m w A ≠ 0 := fun hz => hA ((finiteReplication_zero_iff m w hw A).mp hz)
    simp only [NLA.RA03.pivotMass,if_neg hC,if_neg hA,finiteReplication_frobenius m w hw,
      finiteReplication_entry_normSq]
    have he : ∀ a b : Fin (replicationDimension m),
        (w ((replicationLabels m).symm a).1)^2*(w ((replicationLabels m).symm b).1)^2*
          Complex.normSq (A ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1) /
            NLA.RA03.frobeniusSq A*F ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1 =
        (w ((replicationLabels m).symm a).1)^2*(w ((replicationLabels m).symm b).1)^2*
          (Complex.normSq (A ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1) /
            NLA.RA03.frobeniusSq A*F ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1) := by
      intro a b
      ring
    simp_rw [he]
    exact sum_double_copy_weights m w hw (fun i j => Complex.normSq (A i j)/NLA.RA03.frobeniusSq A*F i j)

#print axioms finiteReplication_lu_mass_sum
end NLA.RA02.Paper
