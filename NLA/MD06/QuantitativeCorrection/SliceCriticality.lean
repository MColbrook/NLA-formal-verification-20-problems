module

public import NLA.MD06.QuantitativeCorrection.CompactBall
public import NLA.MD06.GraphCriticalityHessian.GradientPairing
public import NLA.MD06.GraphCriticalityHessian.PositiveCosineMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open Set Filter WithLp
open scoped BigOperators Topology
open Reference.MD06Actual

theorem actual_interior_slice_minimizer_directional_force_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (phi h : Configuration n) (rho : ℝ) (hzero : (∑ i, h i) = 0) (hnorm : ‖h‖ < rho)
    (hmin : ∀ g ∈ CorrectionBall n rho, LiftedEnergy G (phi+h) ≤ LiftedEnergy G (phi+g))
    (z : Configuration n) (hz : (∑ i, z i) = 0) :
    LineForce G (fun i => phi i+h i) (fun i => z i) 0 = 0 := by
  have hl : ∀ t : ℝ, LineEnergy G (fun i => phi i+h i) (fun i => z i) t =
      LiftedEnergy G (phi+(h+t • z)) := by
    intro t
    rw [line_energy_actual]
    unfold LiftedEnergy
    congr 1
    funext i
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  have hc : IsOpen {t : ℝ | ‖h+t • z‖ < rho} := isOpen_lt (by fun_prop) continuous_const
  have he : (0 : ℝ) ∈ {t : ℝ | ‖h+t • z‖ < rho} := by simpa using hnorm
  have hm : IsLocalMin (LineEnergy G (fun i => phi i+h i) (fun i => z i)) 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), LineEnergy G (fun i => phi i+h i) (fun i => z i) 0 ≤
      LineEnergy G (fun i => phi i+h i) (fun i => z i) t
    filter_upwards [hc.mem_nhds he] with t ht
    have hb : h+t • z ∈ CorrectionBall n rho := by
      constructor
      · simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
          ← Finset.mul_sum,hzero,hz,mul_zero,add_zero]
      · exact ht.le
    calc
      LineEnergy G (fun i => phi i+h i) (fun i => z i) 0 = LiftedEnergy G (phi+h) := by
        rw [hl];simp
      _ ≤ LiftedEnergy G (phi+(h+t • z)) := hmin _ hb
      _ = LineEnergy G (fun i => phi i+h i) (fun i => z i) t := (hl t).symm
  exact hm.hasDerivAt_eq_zero (line_energy_hasDerivAt G _ _ 0)

theorem actual_interior_slice_minimizer_gradient_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (phi h : Configuration n) (rho : ℝ) (hzero : (∑ i, h i) = 0) (hnorm : ‖h‖ < rho)
    (hmin : ∀ g ∈ CorrectionBall n rho, LiftedEnergy G (phi+h) ≤ LiftedEnergy G (phi+g)) :
    ∀ i, Gradient G (PhaseLift (fun a => phi a+h a)) i = 0 := by
  classical
  let theta := PhaseLift (fun a => phi a+h a)
  have he : ∀ i j : Fin n, Gradient G theta i = Gradient G theta j := by
    intro i j
    let z : Configuration n := toLp 2 (Pi.single i (1 : ℝ)-Pi.single j (1 : ℝ))
    have hz : (∑ a, z a) = 0 := by
      simp [z,Finset.sum_sub_distrib]
    have hf := actual_interior_slice_minimizer_directional_force_zero G phi h rho hzero hnorm hmin z hz
    rw [line_force_zero_gradient_pairing] at hf
    have hb : (∑ a, z a * Gradient G theta a) = Gradient G theta i-Gradient G theta j := by
      simp only [z,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]
      simp [Pi.single_apply]
    change (∑ a, z a * Gradient G theta a) = 0 at hf
    exact sub_eq_zero.mp (hb.symm.trans hf)
  intro i
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))
  have hs : (∑ j, Gradient G theta j) = (n : ℝ) * Gradient G theta i := by
    calc
      (∑ j, Gradient G theta j) = ∑ j : Fin n, Gradient G theta i :=
        Finset.sum_congr rfl (fun j _ => he j i)
      _ = (n : ℝ) * Gradient G theta i := by simp
  have hm : (n : ℝ) * Gradient G theta i = 0 := hs.symm.trans (gradient_sum_zero G theta)
  exact (mul_eq_zero.mp hm).resolve_left hn

#print axioms actual_interior_slice_minimizer_directional_force_zero
#print axioms actual_interior_slice_minimizer_gradient_zero
end Reference.MD06Correction
