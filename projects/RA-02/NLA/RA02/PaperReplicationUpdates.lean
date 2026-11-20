module

public import NLA.RA02.PaperReplicationFinite
public import NLA.RA03.Definitions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem finiteReplication_lu_update {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, w i ≠ 0) (A : NLA.RA02.Square n)
    (a b : Fin (replicationDimension m)) :
    NLA.RA03.pivotResidual (finiteReplicatedMatrix m w A) (a,b) =
      finiteReplicatedMatrix m w
        (NLA.RA03.pivotResidual A (((replicationLabels m).symm a).1,((replicationLabels m).symm b).1)) := by
  let g := fun x : Fin (replicationDimension m) => ((replicationLabels m).symm x).1
  have ha : (w (g a) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw (g a))
  have hb : (w (g b) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw (g b))
  by_cases hp : A (g a) (g b)=0
  · have hc : finiteReplicatedMatrix m w A a b=0 := by
      rw [finiteReplicatedMatrix_entry]
      change (w (g a) : ℂ)*A (g a) (g b)*(w (g b) : ℂ)=0
      rw [hp,mul_zero,zero_mul]
    rw [NLA.RA03.pivotResidual,if_pos hc,NLA.RA03.pivotResidual,if_pos hp]
  · have hc : finiteReplicatedMatrix m w A a b ≠ 0 := by
      rw [finiteReplicatedMatrix_entry]
      exact mul_ne_zero (mul_ne_zero ha hp) hb
    rw [NLA.RA03.pivotResidual,if_neg hc,NLA.RA03.pivotResidual,if_neg hp]
    ext x y
    simp only [finiteReplicatedMatrix_entry]
    change (w (g x) : ℂ)*A (g x) (g y)*(w (g y) : ℂ) -
      ((w (g x) : ℂ)*A (g x) (g b)*(w (g b) : ℂ))*
        ((w (g a) : ℂ)*A (g a) (g y)*(w (g y) : ℂ)) /
          ((w (g a) : ℂ)*A (g a) (g b)*(w (g b) : ℂ)) =
      (w (g x) : ℂ)*(A (g x) (g y)-A (g x) (g b)*A (g a) (g y)/A (g a) (g b))*(w (g y) : ℂ)
    field_simp [ha,hb,hp]

theorem choleskyStep_eq_lu_diagonal {n : ℕ} (A : NLA.RA02.Square n) (j : Fin n) :
    NLA.RA02.choleskyStep A j=NLA.RA03.pivotResidual A (j,j) := rfl

theorem finiteReplication_cholesky_update {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, w i ≠ 0) (A : NLA.RA02.Square n) (a : Fin (replicationDimension m)) :
    NLA.RA02.choleskyStep (finiteReplicatedMatrix m w A) a =
      finiteReplicatedMatrix m w (NLA.RA02.choleskyStep A ((replicationLabels m).symm a).1) := by
  rw [choleskyStep_eq_lu_diagonal,choleskyStep_eq_lu_diagonal]
  exact finiteReplication_lu_update m w hw A a a

#print axioms finiteReplication_lu_update
end NLA.RA02.Paper
