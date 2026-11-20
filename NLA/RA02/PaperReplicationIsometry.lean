module

public import NLA.RA02.PaperReplicationDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem rowReplication_isometry {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2 = 1) :
    (rowReplication m w).conjTranspose * rowReplication m w = 1 := by
  ext i j
  rw [Matrix.mul_apply,Fintype.sum_sigma]
  by_cases hij : i=j
  · subst j
    rw [Finset.sum_eq_single i]
    · simpa [rowReplication,Matrix.conjTranspose_apply,nsmul_eq_mul,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,pow_two]
        using congrArg Complex.ofReal (hw i)
    · intro k _ hki
      simp [rowReplication,Matrix.conjTranspose_apply,hki]
    · simp
  · rw [Matrix.one_apply,if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    by_cases hki : k=i
    · subst k
      simp [rowReplication,Matrix.conjTranspose_apply,hij]
    · simp [rowReplication,Matrix.conjTranspose_apply,hki]

theorem sqrtReplication_weights {n : ℕ} (m : Fin n → ℕ) (hm : ∀ i, 0 < m i) :
    ∀ i, (m i : ℝ)*(Real.sqrt (m i))⁻¹^2 = 1 := by
  intro i
  have hpos : 0 < (m i : ℝ) := by exact_mod_cast hm i
  rw [inv_pow,Real.sq_sqrt hpos.le,mul_inv_cancel₀ (ne_of_gt hpos)]

#print axioms rowReplication_isometry
end NLA.RA02.Paper
