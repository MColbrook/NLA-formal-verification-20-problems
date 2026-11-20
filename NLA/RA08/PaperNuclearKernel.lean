module

public import NLA.RA08.PaperNuclearFamily
public import Mathlib.Algebra.Order.Field.GeomSum

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearHeight_ratio {m : ℕ} (i j : Fin m) (hij : i ≤ j) :
    nuclearHeight j=nuclearHeight i*(1/4 : ℝ)^(j.val-i.val) := by
  unfold nuclearHeight
  have he : j.val+1=(i.val+1)+(j.val-i.val) := by omega
  conv_lhs => rw [he,pow_add]

theorem nuclearKernel_diagonal {m : ℕ} (i : Fin m) : nuclearKernel m i i=1/2 := by
  unfold nuclearKernel
  have hi := ne_of_gt (nuclearHeight_pos i)
  field_simp
  ring

theorem nuclearKernel_positive {m : ℕ} (i j : Fin m) : 0 < nuclearKernel m i j :=
  div_pos (nuclearHeight_pos i) (add_pos (nuclearHeight_pos i) (nuclearHeight_pos j))

theorem nuclearKernel_lt_one {m : ℕ} (i j : Fin m) : nuclearKernel m i j < 1 := by
  unfold nuclearKernel
  rw [div_lt_one (add_pos (nuclearHeight_pos i) (nuclearHeight_pos j))]
  linarith [nuclearHeight_pos j]

theorem nuclearKernel_complement {m : ℕ} (i j : Fin m) :
    nuclearKernel m i j+nuclearKernel m j i=1 := by
  unfold nuclearKernel
  have hd : nuclearHeight i+nuclearHeight j ≠ 0 := ne_of_gt (add_pos (nuclearHeight_pos i) (nuclearHeight_pos j))
  rw [add_comm (nuclearHeight j) (nuclearHeight i)]
  field_simp

theorem nuclearKernel_above_formula {m : ℕ} (i j : Fin m) (hij : i ≤ j) :
    nuclearKernel m i j=1/(1+(1/4 : ℝ)^(j.val-i.val)) := by
  unfold nuclearKernel
  rw [nuclearHeight_ratio i j hij]
  have hi : nuclearHeight i ≠ 0 := ne_of_gt (nuclearHeight_pos i)
  have hs : 1+(1/4 : ℝ)^(j.val-i.val) ≠ 0 := by positivity
  have hd : nuclearHeight i+nuclearHeight i*(1/4 : ℝ)^(j.val-i.val) ≠ 0 :=
    ne_of_gt (add_pos (nuclearHeight_pos i) (mul_pos (nuclearHeight_pos i) (by positivity)))
  field_simp

theorem reciprocal_corner_error_bound (x : ℝ) (hx : 0 ≤ x) :
    |1/(1+x)-1| ≤ x := by
  have hp : 0 < 1+x := by linarith
  have hn : 1/(1+x)-1 ≤ 0 := by
    have h := (div_le_one hp).mpr (by linarith : 1 ≤ 1+x)
    linarith
  rw [abs_of_nonpos hn]
  rw [neg_sub,sub_le_iff_le_add]
  have he : 1/(1+x)+x=(1+x+x^2)/(1+x) := by field_simp;ring
  rw [add_comm x (1/(1+x)),he]
  rw [le_div_iff₀ hp]
  nlinarith [sq_nonneg x]

theorem nuclearKernel_upper_error {m : ℕ} (i j : Fin m) (hij : i ≤ j) :
    |nuclearKernel m i j-1| ≤ (1/4 : ℝ)^(j.val-i.val) := by
  rw [nuclearKernel_above_formula i j hij]
  exact reciprocal_corner_error_bound _ (by positivity)

theorem nuclearKernel_lower_error {m : ℕ} (i j : Fin m) (hji : j ≤ i) :
    |nuclearKernel m i j| ≤ (1/4 : ℝ)^(i.val-j.val) := by
  have hc := nuclearKernel_complement i j
  have hu := nuclearKernel_upper_error j i hji
  rw [abs_of_nonpos (by linarith [nuclearKernel_lt_one j i] : nuclearKernel m j i-1 ≤ 0)] at hu
  rw [abs_of_pos (nuclearKernel_positive i j)]
  linarith

end NLA.RA08.Paper
