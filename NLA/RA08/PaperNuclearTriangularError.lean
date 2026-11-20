module

public import NLA.RA08.PaperNuclearKernel
public import NLA.RA08.PaperNuclearFrobenius

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem finite_geometric_distances {m : ℕ} (s : Finset (Fin m)) (d : Fin m → ℕ)
    (hd : Set.InjOn d (s : Set (Fin m)))
    (hr : ∀ j ∈ s, 1 ≤ d j ∧ d j < m) :
    ∑ j ∈ s, (1/16 : ℝ)^(d j) ≤ 1/15 := by
  have hsub : s.image d ⊆ Finset.Ico 1 m := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Ico.mpr (hr j hj)
  rw [← Finset.sum_image hd]
  calc
    _ ≤ ∑ k ∈ Finset.Ico 1 m, (1/16 : ℝ)^k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ ≤ (1/16 : ℝ)^1/(1-1/16) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = 1/15 := by norm_num

theorem upper_distance_sum {m : ℕ} (i : Fin m) :
    ∑ j : Fin m, (if i < j then (1/16 : ℝ)^(j.val-i.val) else 0) ≤ 1/15 := by
  rw [← Finset.sum_filter]
  apply finite_geometric_distances
  · intro j hj k hk he
    have hj' : i < j := (Finset.mem_filter.mp hj).2
    have hk' : i < k := (Finset.mem_filter.mp hk).2
    change j.val-i.val=k.val-i.val at he
    apply Fin.ext
    omega
  · intro j hj
    have hj' : i < j := (Finset.mem_filter.mp hj).2
    constructor <;> omega

theorem lower_distance_sum {m : ℕ} (i : Fin m) :
    ∑ j : Fin m, (if j < i then (1/16 : ℝ)^(i.val-j.val) else 0) ≤ 1/15 := by
  rw [← Finset.sum_filter]
  apply finite_geometric_distances
  · intro j hj k hk he
    have hj' : j < i := (Finset.mem_filter.mp hj).2
    have hk' : k < i := (Finset.mem_filter.mp hk).2
    change i.val-j.val=i.val-k.val at he
    apply Fin.ext
    omega
  · intro j hj
    have hj' : j < i := (Finset.mem_filter.mp hj).2
    constructor <;> omega

theorem nuclearTriangular_error_entry {m : ℕ} (i j : Fin m) :
    ((nuclearKernel m-(nuclearTriangular m-(1/2 : ℝ) • (1 : RealMatrix m))) i j)^2 ≤
      (if i < j then (1/16 : ℝ)^(j.val-i.val) else 0)+
      (if j < i then (1/16 : ℝ)^(i.val-j.val) else 0) := by
  have hp (d : ℕ) : ((1/4 : ℝ)^d)^2=(1/16 : ℝ)^d := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rcases lt_trichotomy i j with hij|hij|hji
  · have hne : i ≠ j := ne_of_lt hij
    simp only [Matrix.sub_apply,nuclearTriangular,if_pos hij.le,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply_ne hne,mul_zero,sub_zero,if_pos hij,if_neg (not_lt_of_ge hij.le),add_zero]
    have hs := mul_self_le_mul_self (abs_nonneg (nuclearKernel m i j-1))
      (nuclearKernel_upper_error i j hij.le)
    simpa only [← pow_two,sq_abs,hp] using hs
  · subst j
    norm_num [nuclearKernel_diagonal,nuclearTriangular]
  · have hne : i ≠ j := Ne.symm (ne_of_lt hji)
    simp only [Matrix.sub_apply,nuclearTriangular,if_neg (not_le_of_gt hji),Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply_ne hne,mul_zero,sub_zero,if_pos hji,if_neg (not_lt_of_ge hji.le),zero_add]
    have hs := mul_self_le_mul_self (abs_nonneg (nuclearKernel m i j))
      (nuclearKernel_lower_error i j hji.le)
    simpa only [← pow_two,sq_abs,hp] using hs

theorem nuclearTriangular_error_frobenius_squared (m : ℕ) :
    frobeniusSquared (nuclearKernel m-(nuclearTriangular m-(1/2 : ℝ) • (1 : RealMatrix m))) ≤
      2*m/15 := by
  unfold frobeniusSquared
  calc
    _ ≤ ∑ i : Fin m, (∑ j : Fin m,
        ((if i < j then (1/16 : ℝ)^(j.val-i.val) else 0)+
        (if j < i then (1/16 : ℝ)^(i.val-j.val) else 0))) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _ => nuclearTriangular_error_entry i j
    _ ≤ ∑ _i : Fin m, (2/15 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.sum_add_distrib]
      have hu := upper_distance_sum i
      have hl := lower_distance_sum i
      linarith
    _ = 2*m/15 := by simp;ring

#print axioms nuclearTriangular_error_frobenius_squared
end NLA.RA08.Paper
