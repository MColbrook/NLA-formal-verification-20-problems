module

public import NLA.RA02.PaperReplicationFinite

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem sum_copy_weights {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (f : Fin n → ℝ) :
    (∑ a : Fin (replicationDimension m),
      (w ((replicationLabels m).symm a).1)^2*f ((replicationLabels m).symm a).1) = ∑ i, f i := by
  change (∑ a : Fin (replicationDimension m),
    (fun x : ReplicatedRows m => (w x.1)^2*f x.1) ((replicationLabels m).symm a)) = _
  rw [(replicationLabels m).symm.sum_comp (fun x : ReplicatedRows m => (w x.1)^2*f x.1),Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc,hw,one_mul]

theorem sum_double_copy_weights {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (F : Fin n → Fin n → ℝ) :
    (∑ a : Fin (replicationDimension m), ∑ b : Fin (replicationDimension m),
      (w ((replicationLabels m).symm a).1)^2*(w ((replicationLabels m).symm b).1)^2*
        F ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1) = ∑ i, ∑ j, F i j := by
  have hb : ∀ a : Fin (replicationDimension m),
      (∑ b : Fin (replicationDimension m),
        (w ((replicationLabels m).symm a).1)^2*(w ((replicationLabels m).symm b).1)^2*
          F ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1) =
      (w ((replicationLabels m).symm a).1)^2*∑ j, F ((replicationLabels m).symm a).1 j := by
    intro a
    calc
      _ = (w ((replicationLabels m).symm a).1)^2*
          ∑ b : Fin (replicationDimension m),
            (w ((replicationLabels m).symm b).1)^2*F ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [sum_copy_weights m w hw]
  simp_rw [hb]
  exact sum_copy_weights m w hw (fun i => ∑ j, F i j)

theorem copy_weights_ne_zero {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) : ∀ i, w i ≠ 0 := by
  intro i hz
  have hi := hw i
  rw [hz] at hi
  norm_num at hi

#print axioms sum_double_copy_weights
end NLA.RA02.Paper
