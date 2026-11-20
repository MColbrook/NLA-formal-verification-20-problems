module

public import NLA.RA08.PaperDerivativeDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

theorem clippingDividedDifference_absolute (x y : ℝ) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    clippingDividedDifference x y =
      (1/2 : ℝ)*(1-(x+y-2)/(|x-1|+|y-1|)) := by
  have hden : |x-1|+|y-1| ≠ 0 := ne_of_gt (add_pos
    (abs_pos.mpr (sub_ne_zero.mpr hx1)) (abs_pos.mpr (sub_ne_zero.mpr hy1)))
  by_cases hxy : x = y
  · subst y
    by_cases hx : x < 1
    · rw [clippingDividedDifference,if_pos rfl,if_pos hx,
        abs_of_neg (by linarith : x-1 < 0)]
      rw [abs_of_neg (by linarith : x-1 < 0)] at hden
      field_simp [hden]
      ring
    · have hxgt : 1 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx1)
      rw [clippingDividedDifference,if_pos rfl,if_neg hx,
        abs_of_pos (by linarith : 0 < x-1)]
      rw [abs_of_pos (by linarith : 0 < x-1)] at hden
      field_simp [hden]
      ring
  · rw [clippingDividedDifference,if_neg hxy]
    have hd : x-y ≠ 0 := sub_ne_zero.mpr hxy
    by_cases hx : x < 1 <;> by_cases hy : y < 1
    · rw [witnessFunction,witnessFunction,min_eq_left hx.le,min_eq_left hy.le,
        abs_of_neg (by linarith : x-1 < 0),abs_of_neg (by linarith : y-1 < 0)]
      rw [abs_of_neg (by linarith : x-1 < 0),abs_of_neg (by linarith : y-1 < 0)] at hden
      field_simp [hden]
      ring
    · have hygt : 1 < y := lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm hy1)
      rw [witnessFunction,witnessFunction,min_eq_left hx.le,min_eq_right hygt.le,
        abs_of_neg (by linarith : x-1 < 0),abs_of_pos (by linarith : 0 < y-1)]
      rw [abs_of_neg (by linarith : x-1 < 0),abs_of_pos (by linarith : 0 < y-1)] at hden
      field_simp [hden]
      ring
    · have hxgt : 1 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx1)
      rw [witnessFunction,witnessFunction,min_eq_right hxgt.le,min_eq_left hy.le,
        abs_of_pos (by linarith : 0 < x-1),abs_of_neg (by linarith : y-1 < 0)]
      rw [abs_of_pos (by linarith : 0 < x-1),abs_of_neg (by linarith : y-1 < 0)] at hden
      field_simp [hden]
      ring
    · have hxgt : 1 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx1)
      have hygt : 1 < y := lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm hy1)
      rw [witnessFunction,witnessFunction,min_eq_right hxgt.le,min_eq_right hygt.le,
        abs_of_pos (by linarith : 0 < x-1),abs_of_pos (by linarith : 0 < y-1)]
      rw [abs_of_pos (by linarith : 0 < x-1),abs_of_pos (by linarith : 0 < y-1)] at hden
      field_simp [hden]
      ring

#print axioms clippingDividedDifference_absolute
end NLA.RA08.Paper
