module

public import NLA.MD06.GraphCriticalityHessian.LiftTopology
public import NLA.MD06.GraphCriticalityHessian.SecondDerivative
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual
open Set Filter
open scoped Topology BigOperators

theorem actual_positive_cosine_critical_real_minimum {n : ℕ} (G : SimpleGraph (Fin n))
    (phi : Fin n → ℝ) (hcrit : ∀ i, Gradient G (PhaseLift phi) i = 0)
    (hcos : ∀ i j, G.Adj i j → 0 < Real.Angle.cos (PhaseLift phi i-PhaseLift phi j)) :
    IsLocalMin (RealEnergy G) phi := by
  classical
  let U : Set (Fin n → ℝ) := {psi | ∀ i j, G.Adj i j → 0 < Real.cos (psi i-psi j)}
  have hU : IsOpen U := by
    simp only [U,Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (show Continuous (fun psi : Fin n → ℝ => Real.cos (psi i-psi j)) by fun_prop)
  have hp : phi ∈ U := by
    intro i j hij
    simpa only [PhaseLift,← Real.Angle.coe_sub,Real.Angle.cos_coe] using hcos i j hij
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  change ∀ᶠ psi in 𝓝 phi, RealEnergy G phi ≤ RealEnergy G psi
  filter_upwards [Metric.ball_mem_nhds phi hδ] with psi hpsi
  let z : Fin n → ℝ := fun i => psi i-phi i
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, (fun i => phi i+t*z i) ∈ U := by
    intro t ht
    have hl := (convex_ball phi δ).lineMap_mem (Metric.mem_ball_self hδ) hpsi ht
    have he : (fun i => phi i+t*z i) = AffineMap.lineMap phi psi t := by
      funext i
      simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,z]
      ring
    exact hball (he.symm ▸ hl)
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ LineCurvature G phi z t := by
    intro t ht
    unfold LineCurvature
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases he : i < j ∧ G.Adj i j
    · simp only [if_pos he]
      have hc : 0 < Real.cos (phi i-phi j+t*(z i-z j)) := by
        have hh := hline t ht i j he.2
        convert hh using 1
        congr 1
        ring
      exact mul_nonneg hc.le (sq_nonneg _)
    · simp only [if_neg he,le_refl]
  have hzero : LineForce G phi z 0 = 0 :=
    (actual_critical_iff_all_line_forces_zero G phi).mp hcrit z
  have he := nonnegative_second_derivative_minimum (LineEnergy G phi z) (LineForce G phi z)
    (LineCurvature G phi z) (line_energy_hasDerivAt G phi z) (line_force_hasDerivAt G phi z) hzero hpos
  have he0 : LineEnergy G phi z 0 = RealEnergy G phi := by
    rw [line_energy_actual]
    simp only [zero_mul,add_zero]
  have he1 : LineEnergy G phi z 1 = RealEnergy G psi := by
    rw [line_energy_actual]
    congr 1
    funext i
    simp only [one_mul,z]
    ring
  simpa only [he0,he1] using he

theorem actual_positive_cosine_critical_angle_minimum {n : ℕ} (G : SimpleGraph (Fin n))
    (theta : Phase n) (hcrit : ∀ i, Gradient G theta i = 0)
    (hcos : ∀ i j, G.Adj i j → 0 < Real.Angle.cos (theta i-theta j)) :
    IsLocalMin (Energy G) theta := by
  let phi : Fin n → ℝ := fun i => (theta i).toReal
  have he : PhaseLift phi = theta := by funext i; exact Real.Angle.coe_toReal (theta i)
  have hc : ∀ i, Gradient G (PhaseLift phi) i = 0 := he.symm ▸ hcrit
  have hp : ∀ i j, G.Adj i j → 0 < Real.Angle.cos (PhaseLift phi i-PhaseLift phi j) := he.symm ▸ hcos
  have hm := actual_positive_cosine_critical_real_minimum G phi hc hp
  have ht := (actual_local_min_real_lift_iff G phi).mp hm
  rwa [he] at ht

#print axioms actual_positive_cosine_critical_real_minimum
#print axioms actual_positive_cosine_critical_angle_minimum
end Reference.MD06Actual
