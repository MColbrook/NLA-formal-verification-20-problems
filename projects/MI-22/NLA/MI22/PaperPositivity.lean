module

public import NLA.MI22.PaperWitnessDefinitions
public import NLA.MI22.Witness
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI22.Paper

private def paperB_floorL : Mat 3 :=
  !![1, 0, 0;
    (-4096 / 17407), 1, 0;
    0, (-146020499456 / 292042029057), 1]

private def paperB_floorD : Mat 3 :=
  Matrix.diagonal (![(17407 / 1024), (292042029057 / 17824768), (4028699265023 / 299051037754368)] : Fin 3 → ℂ)

private theorem paperB_floor_ldl :
    paperB - (1/1024 : ℝ) • (1 : Mat 3) = paperB_floorL * paperB_floorD * paperB_floorL.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperB, paperC, paperR, paperS, paperB_floorL, paperB_floorD,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

theorem paperB_floor_posDef : (paperB - (1/1024 : ℝ) • (1 : Mat 3)).PosDef := by
  rw [paperB_floor_ldl]
  have hd : paperB_floorD.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.pos_iff, paperB_floorD]
  have hl : IsUnit paperB_floorL := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : paperB_floorL.det = (1 : ℂ) := by
      norm_num [paperB_floorL, Matrix.det_fin_three, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
    rw [hdet]
    exact isUnit_one
  exact hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hl)

#print axioms paperB_floor_posDef

private def paperC_floorL : Mat 3 :=
  !![1, 0, 0;
    (-4096 / 67), 1, 0;
    0, (-8992587776 / 287763595197), 1]

private def paperC_floorD : Mat 3 :=
  Matrix.diagonal (![(67 / 1024), (287763595197 / 68608), (3010490269763 / 294669921481728)] : Fin 3 → ℂ)

private theorem paperC_floor_ldl :
    paperC - (1/1024 : ℝ) • (1 : Mat 3) = paperC_floorL * paperC_floorD * paperC_floorL.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperB, paperC, paperR, paperS, paperC_floorL, paperC_floorD,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

theorem paperC_floor_posDef : (paperC - (1/1024 : ℝ) • (1 : Mat 3)).PosDef := by
  rw [paperC_floor_ldl]
  have hd : paperC_floorD.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.pos_iff, paperC_floorD]
  have hl : IsUnit paperC_floorL := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : paperC_floorL.det = (1 : ℂ) := by
      norm_num [paperC_floorL, Matrix.det_fin_three, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
    rw [hdet]
    exact isUnit_one
  exact hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hl)

#print axioms paperC_floor_posDef

private def paperR_lowerL : Mat 3 :=
  !![1, 0, 0;
    (-4774979464975 / 113431071954661), 1, 0;
    (-152620714401404 / 113431071954661), (-21764474078260176797712449406 / 711445064412215186343547828189), 1]

private def paperR_lowerD : Mat 3 :=
  Matrix.diagonal (![(113431071954661 / 1000000000000000), (711445064412215186343547828189 / 113431071954661000000000000000), (93973764180285316872142360263076834965905753 / 711445064412215186343547828189000000000000000)] : Fin 3 → ℂ)

private theorem paperR_lower_ldl :
    paperR - (9/20 : ℝ) • (1 : Mat 3) = paperR_lowerL * paperR_lowerD * paperR_lowerL.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperB, paperC, paperR, paperS, paperR_lowerL, paperR_lowerD,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

theorem paperR_lower_posDef : (paperR - (9/20 : ℝ) • (1 : Mat 3)).PosDef := by
  rw [paperR_lower_ldl]
  have hd : paperR_lowerD.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.pos_iff, paperR_lowerD]
  have hl : IsUnit paperR_lowerL := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : paperR_lowerL.det = (1 : ℂ) := by
      norm_num [paperR_lowerL, Matrix.det_fin_three, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
    rw [hdet]
    exact isUnit_one
  exact hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hl)

#print axioms paperR_lower_posDef

private def paperS_lowerL : Mat 3 :=
  !![1, 0, 0;
    (-40084698659651 / 967565567728212), 1, 0;
    (-13229218267437 / 161260927954702), (-1116357102308959154814207785262 / 2352981841547917079567431542719), 1]

private def paperS_lowerD : Mat 3 :=
  Matrix.diagonal (![(241891391932053 / 250000000000000), (2352981841547917079567431542719 / 967565567728212000000000000000), (90451917005419531313481056972446290542910901 / 588245460386979269891857885679750000000000000)] : Fin 3 → ℂ)

private theorem paperS_lower_ldl :
    paperS - (9/20 : ℝ) • (1 : Mat 3) = paperS_lowerL * paperS_lowerD * paperS_lowerL.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperB, paperC, paperR, paperS, paperS_lowerL, paperS_lowerD,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

theorem paperS_lower_posDef : (paperS - (9/20 : ℝ) • (1 : Mat 3)).PosDef := by
  rw [paperS_lower_ldl]
  have hd : paperS_lowerD.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.pos_iff, paperS_lowerD]
  have hl : IsUnit paperS_lowerL := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : paperS_lowerL.det = (1 : ℂ) := by
      norm_num [paperS_lowerL, Matrix.det_fin_three, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
    rw [hdet]
    exact isUnit_one
  exact hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hl)

#print axioms paperS_lower_posDef

private def paperR_upperL : Mat 3 :=
  !![1, 0, 0;
    (4774979464975 / 7436568928045339), 1, 0;
    (152620714401404 / 7436568928045339), (1378377768133042123202287550594 / 9502064700834720936343547828189), 1]

private def paperR_upperD : Mat 3 :=
  Matrix.diagonal (![(7436568928045339 / 1000000000000000), (9502064700834720936343547828189 / 7436568928045339000000000000000), (68193202340067767725141134524649523165034094247 / 9502064700834720936343547828189000000000000000)] : Fin 3 → ℂ)

private theorem paperR_upper_ldl :
    (8 : ℝ) • (1 : Mat 3) - paperR = paperR_upperL * paperR_upperD * paperR_upperL.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperB, paperC, paperR, paperS, paperR_upperL, paperR_upperD,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

theorem paperR_upper_posDef : ((8 : ℝ) • (1 : Mat 3) - paperR).PosDef := by
  rw [paperR_upper_ldl]
  have hd : paperR_upperD.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.pos_iff, paperR_upperD]
  have hl : IsUnit paperR_upperL := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : paperR_upperL.det = (1 : ℂ) := by
      norm_num [paperR_upperL, Matrix.det_fin_three, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
    rw [hdet]
    exact isUnit_one
  exact hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hl)

#print axioms paperR_upper_posDef

private def paperS_upperL : Mat 3 :=
  !![1, 0, 0;
    (40084698659651 / 2582434432271788), 1, 0;
    (39687654802311 / 1291217216135894), (2967885541757220595185792214738 / 2881633710831768979567431542719), 1]

private def paperS_upperD : Mat 3 :=
  Matrix.diagonal (![(645608608067947 / 250000000000000), (2881633710831768979567431542719 / 2582434432271788000000000000000), (1193156235152734906305632446485828709457089099 / 720408427707942244891857885679750000000000000)] : Fin 3 → ℂ)

private theorem paperS_upper_ldl :
    (4 : ℝ) • (1 : Mat 3) - paperS = paperS_upperL * paperS_upperD * paperS_upperL.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperB, paperC, paperR, paperS, paperS_upperL, paperS_upperD,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMul_diagonal,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_ofNat]

theorem paperS_upper_posDef : ((4 : ℝ) • (1 : Mat 3) - paperS).PosDef := by
  rw [paperS_upper_ldl]
  have hd : paperS_upperD.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.pos_iff, paperS_upperD]
  have hl : IsUnit paperS_upperL := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : paperS_upperL.det = (1 : ℂ) := by
      norm_num [paperS_upperL, Matrix.det_fin_three, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
    rw [hdet]
    exact isUnit_one
  exact hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hl)

#print axioms paperS_upper_posDef

end NLA.MI22.Paper
