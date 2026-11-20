module

public import NLA.MD06.GraphCriticalityHessian.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual
open scoped BigOperators

theorem real_energy_angle_lift {n : ℕ} (G : SimpleGraph (Fin n)) (phi : Fin n → ℝ) :
    RealEnergy G phi = Energy G (fun i => (phi i : Real.Angle)) := by
  simp only [RealEnergy,Energy,← Real.Angle.coe_sub,Real.Angle.cos_coe]

theorem line_energy_actual {n : ℕ} (G : SimpleGraph (Fin n)) (phi z : Fin n → ℝ) (t : ℝ) :
    LineEnergy G phi z t = RealEnergy G (fun i => phi i + t*z i) := by
  classical
  unfold LineEnergy RealEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> congr 1
  congr 1
  ring

theorem line_energy_hasDerivAt {n : ℕ} (G : SimpleGraph (Fin n)) (phi z : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (LineEnergy G phi z) (LineForce G phi z t) t := by
  classical
  unfold LineEnergy LineForce
  apply HasDerivAt.fun_sum (𝕜 := ℝ) (F := ℝ)
  intro i _
  apply HasDerivAt.fun_sum (𝕜 := ℝ) (F := ℝ)
  intro j _
  by_cases he : i < j ∧ G.Adj i j
  · simp only [if_pos he]
    have hd : HasDerivAt (fun u : ℝ => phi i-phi j+u*(z i-z j)) (z i-z j) t := by
      convert! ((hasDerivAt_id t).mul_const (z i-z j)).const_add (phi i-phi j) using 1
      simp
    convert! (hasDerivAt_const t (1 : ℝ)).sub hd.cos using 1
    simp
  · simp only [if_neg he]
    exact hasDerivAt_const t 0

theorem line_force_hasDerivAt {n : ℕ} (G : SimpleGraph (Fin n)) (phi z : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (LineForce G phi z) (LineCurvature G phi z t) t := by
  classical
  unfold LineForce LineCurvature
  apply HasDerivAt.fun_sum (𝕜 := ℝ) (F := ℝ)
  intro i _
  apply HasDerivAt.fun_sum (𝕜 := ℝ) (F := ℝ)
  intro j _
  by_cases he : i < j ∧ G.Adj i j
  · simp only [if_pos he]
    have hd : HasDerivAt (fun u : ℝ => phi i-phi j+u*(z i-z j)) (z i-z j) t := by
      convert! ((hasDerivAt_id t).mul_const (z i-z j)).const_add (phi i-phi j) using 1
      simp
    convert! hd.sin.mul_const (z i-z j) using 1
    ring
  · simp only [if_neg he]
    exact hasDerivAt_const t 0

theorem line_curvature_actual_hessian {n : ℕ} (G : SimpleGraph (Fin n))
    (phi z : Fin n → ℝ) (t : ℝ) :
    LineCurvature G phi z t = HessianQuadratic G (fun i => ((phi i+t*z i : ℝ) : Real.Angle)) z := by
  classical
  unfold LineCurvature HessianQuadratic
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [← Real.Angle.coe_sub,Real.Angle.cos_coe]
  split_ifs <;> congr 1
  congr 1
  ring

#print axioms real_energy_angle_lift
#print axioms line_energy_actual
#print axioms line_energy_hasDerivAt
#print axioms line_force_hasDerivAt
#print axioms line_curvature_actual_hessian
end Reference.MD06Actual
