module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem rational_positive_num (q : ℚ) (hq : 0 < q) : 0 < q.num := by
  have hd : 0 < (q.den : ℚ) := by exact_mod_cast q.den_pos
  have he : 0 < (q.num : ℚ)/(q.den : ℚ) := by rw [q.num_div_den]; exact hq
  have hn : 0 < (q.num : ℚ) := (div_pos_iff_of_pos_right hd).mp he
  exact_mod_cast hn

theorem exists_rational_copy_counts {n : ℕ} (q : Fin n → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ (c : ℚ) (m : Fin n → ℕ), 0 < c ∧ (∀ i, 0 < m i) ∧
      ∀ i, q i=c*(m i : ℚ) := by
  let D : ℕ := ∏ i, (q i).den
  let P : Fin n → ℕ := fun i => ∏ j ∈ Finset.univ.erase i, (q j).den
  let m : Fin n → ℕ := fun i => (q i).num.toNat*P i
  have hD : 0 < D := Finset.prod_pos (fun i _ => (q i).den_pos)
  have hP : ∀ i, 0 < P i := fun i => Finset.prod_pos (fun j _ => (q j).den_pos)
  have hDP : ∀ i, D=(q i).den*P i := fun i =>
    (Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)).symm
  refine ⟨(D : ℚ)⁻¹,m,inv_pos.mpr (by exact_mod_cast hD),?_,?_⟩
  · intro i
    have hn : 0 < (q i).num := rational_positive_num _ (hq i)
    have hnn : 0 < (q i).num.toNat := by omega
    exact Nat.mul_pos hnn (hP i)
  · intro i
    have hnum : 0 ≤ (q i).num := (rational_positive_num _ (hq i)).le
    have hn : ((q i).num.toNat : ℚ)=((q i).num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum
    have hd : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
    have hp : (P i : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hP i))
    have hdc : (D : ℚ)=((q i).den : ℚ)*(P i : ℚ) := by exact_mod_cast hDP i
    change q i=(D : ℚ)⁻¹*((q i).num.toNat*P i : ℕ)
    calc
      q i=((q i).num : ℚ)/((q i).den : ℚ) := (q i).num_div_den.symm
      _ = _ := by rw [Nat.cast_mul,hn,hdc]; field_simp [hd,hp]

#print axioms exists_rational_copy_counts
end NLA.RA02.Paper
