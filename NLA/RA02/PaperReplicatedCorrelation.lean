module

public import NLA.RA02.PaperReplicatedCorrelationDefinitions
public import NLA.RA02.PaperReplicationFinite
public import NLA.RA02.PaperCorrelationRegularization

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem replicatedCorrelation_posSemidef {n : ℕ} (m : Fin n → ℕ) (c : ℝ)
    (hc : 0 < c) (A : NLA.RA02.Square n) (hA : A.PosSemidef) :
    (replicatedCorrelation m c A).PosSemidef :=
  (finiteReplicatedMatrix_posSemidef m _ A hA).smul (inv_nonneg.mpr hc.le)

theorem replicatedCorrelation_unitDiagonal {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (hc : 0 < c) (A : NLA.RA02.Square n)
    (hd : ∀ i, A i i = ((c*(m i : ℝ) : ℝ) : ℂ)) :
    ∀ a, replicatedCorrelation m c A a a = 1 := by
  intro a
  let i := ((replicationLabels m).symm a).1
  let w := (Real.sqrt (m i))⁻¹
  have hw : (m i : ℝ)*w^2=1 := sqrtReplication_weights m hm i
  have he : c⁻¹*(w*(c*(m i : ℝ))*w)=1 := by
    calc
      _ = (c⁻¹*c)*((m i : ℝ)*w^2) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt hc),hw,mul_one]
  simp only [replicatedCorrelation,Matrix.smul_apply]
  rw [finiteReplicatedMatrix_entry,hd]
  simpa only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_one,i,w]
    using congrArg Complex.ofReal he

theorem replicatedCorrelation_realPositive {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (hc : 0 < c) (A : NLA.RA02.Square n)
    (hA : ∀ i j, (A i j).im=0 ∧ 0 < (A i j).re) :
    ∀ a b, (replicatedCorrelation m c A a b).im=0 ∧
      0 < (replicatedCorrelation m c A a b).re := by
  intro a b
  let i := ((replicationLabels m).symm a).1
  let j := ((replicationLabels m).symm b).1
  have hi : 0 < (Real.sqrt (m i))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hm i))
  have hj : 0 < (Real.sqrt (m j))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hm j))
  have he : A i j = ((A i j).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (hA i j).1
  have hv : replicatedCorrelation m c A a b =
      ((c⁻¹*((Real.sqrt (m i))⁻¹*(A i j).re*(Real.sqrt (m j))⁻¹) : ℝ) : ℂ) := by
    simp only [replicatedCorrelation,Matrix.smul_apply]
    rw [finiteReplicatedMatrix_entry]
    change (c⁻¹ : ℝ) • ((((Real.sqrt (m i))⁻¹ : ℝ) : ℂ)*A i j*
      (((Real.sqrt (m j))⁻¹ : ℝ) : ℂ)) = _
    rw [he]
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_re]
  rw [hv]
  exact ⟨rfl,mul_pos (inv_pos.mpr hc) (mul_pos (mul_pos hi (hA i j).2) hj)⟩

theorem regularized_replicatedCorrelation_properties {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (hc : 0 < c) (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (hp : ∀ i j, (A i j).im=0 ∧ 0 < (A i j).re)
    (hd : ∀ i, A i i = ((c*(m i : ℝ) : ℝ) : ℂ)) {δ : ℝ} (hδ : 0 < δ) :
    (regularizedCorrelation (replicatedCorrelation m c A) δ).PosDef ∧
    (∀ a b, (regularizedCorrelation (replicatedCorrelation m c A) δ a b).im=0 ∧
      0 < (regularizedCorrelation (replicatedCorrelation m c A) δ a b).re) ∧
    (∀ a, regularizedCorrelation (replicatedCorrelation m c A) δ a a=1) :=
  ⟨regularizedCorrelation_posDef _ (replicatedCorrelation_posSemidef m c hc A hA) hδ,
   regularizedCorrelation_realPositive _ (replicatedCorrelation_realPositive m hm c hc A hp) hδ,
   regularizedCorrelation_unitDiagonal _ (replicatedCorrelation_unitDiagonal m hm c hc A hd) hδ⟩

#print axioms regularized_replicatedCorrelation_properties
end NLA.RA02.Paper
