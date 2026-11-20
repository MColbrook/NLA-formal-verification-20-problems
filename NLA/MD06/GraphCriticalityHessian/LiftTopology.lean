module

public import NLA.MD06.GraphCriticalityHessian.LiftDefinitions
public import NLA.MD06.GraphCriticalityHessian.LocalMinimumCriticality
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual
open Filter
open scoped Topology

theorem angle_coe_isOpenMap : IsOpenMap ((↑) : ℝ → Real.Angle) := by
  change IsOpenMap ((↑) : ℝ → ℝ ⧸ AddSubgroup.zmultiples (2*Real.pi))
  exact QuotientAddGroup.isOpenMap_coe

theorem phase_lift_continuous (n : ℕ) : Continuous (PhaseLift (n := n)) := by
  apply continuous_pi
  intro i
  exact Real.Angle.continuous_coe.comp (continuous_apply i)

theorem phase_lift_isOpenMap (n : ℕ) : IsOpenMap (PhaseLift (n := n)) := by
  change IsOpenMap (Pi.map (fun _ : Fin n => ((↑) : ℝ → Real.Angle)))
  apply IsOpenMap.piMap
  · exact fun _ => angle_coe_isOpenMap
  · exact Filter.Eventually.of_forall (fun _ theta => ⟨theta.toReal,Real.Angle.coe_toReal theta⟩)

theorem actual_local_min_real_lift_iff {n : ℕ} (G : SimpleGraph (Fin n)) (phi : Fin n → ℝ) :
    IsLocalMin (RealEnergy G) phi ↔ IsLocalMin (Energy G) (PhaseLift phi) := by
  constructor
  · intro h
    change ∀ᶠ theta in 𝓝 (PhaseLift phi), Energy G (PhaseLift phi) ≤ Energy G theta
    rw [← (phase_lift_isOpenMap n).map_nhds_eq (phase_lift_continuous n).continuousAt]
    change ∀ᶠ psi in 𝓝 phi, Energy G (PhaseLift phi) ≤ Energy G (PhaseLift psi)
    change ∀ᶠ psi in 𝓝 phi, RealEnergy G phi ≤ RealEnergy G psi at h
    exact h.mono (fun psi hpsi => by
      calc
        Energy G (PhaseLift phi) = RealEnergy G phi := (real_energy_angle_lift G phi).symm
        _ ≤ RealEnergy G psi := hpsi
        _ = Energy G (PhaseLift psi) := real_energy_angle_lift G psi)
  · intro h
    have hm := h.comp_continuous (phase_lift_continuous n).continuousAt
    have hf : RealEnergy G = Energy G ∘ PhaseLift := by
      funext psi
      exact real_energy_angle_lift G psi
    rw [← hf] at hm
    exact hm

#print axioms angle_coe_isOpenMap
#print axioms phase_lift_continuous
#print axioms phase_lift_isOpenMap
#print axioms actual_local_min_real_lift_iff
end Reference.MD06Actual
