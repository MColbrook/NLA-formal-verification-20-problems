module

public import NLA.MD06.QuantitativeCorrection.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open Set
open scoped BigOperators Topology

theorem actual_lifted_energy_continuous {n : ℕ} (G : SimpleGraph (Fin n)) :
    Continuous (LiftedEnergy G) := by
  classical
  unfold LiftedEnergy Reference.MD06Actual.RealEnergy
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs
  · fun_prop
  · exact continuous_const

theorem actual_mean_zero_ball_compact (n : ℕ) (rho : ℝ) :
    IsCompact (CorrectionBall n rho) := by
  have hz : IsClosed {h : Configuration n | (∑ i, h i) = 0} := by
    exact isClosed_eq (by fun_prop) continuous_const
  have he : CorrectionBall n rho = Metric.closedBall (0 : Configuration n) rho ∩
      {h : Configuration n | (∑ i, h i) = 0} := by
    ext h
    simp only [CorrectionBall,Set.mem_ofPred,Set.mem_inter_iff,Metric.mem_closedBall,
      dist_zero_right,and_comm]
  rw [he]
  exact (isCompact_closedBall (0 : Configuration n) rho).inter_right hz

theorem actual_mean_zero_ball_energy_minimizer {n : ℕ} (G : SimpleGraph (Fin n))
    (phi : Configuration n) (rho : ℝ) (hrho : 0 ≤ rho) :
    ∃ h : Configuration n, (∑ i, h i) = 0 ∧ ‖h‖ ≤ rho ∧
      ∀ g ∈ CorrectionBall n rho, LiftedEnergy G (phi+h) ≤ LiftedEnergy G (phi+g) := by
  have hn : (CorrectionBall n rho).Nonempty := by
    refine ⟨0,?_⟩
    simp [CorrectionBall,hrho]
  have hc : Continuous (fun h : Configuration n => LiftedEnergy G (phi+h)) :=
    (actual_lifted_energy_continuous G).comp (by fun_prop)
  obtain ⟨h,hh,hm⟩ := (actual_mean_zero_ball_compact n rho).exists_isMinOn hn hc.continuousOn
  exact ⟨h,hh.1,hh.2,fun g hg => hm hg⟩

#print axioms actual_lifted_energy_continuous
#print axioms actual_mean_zero_ball_compact
#print axioms actual_mean_zero_ball_energy_minimizer
end Reference.MD06Correction
