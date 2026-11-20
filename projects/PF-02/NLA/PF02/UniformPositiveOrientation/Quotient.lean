module

public import NLA.PF02.UniformPositiveOrientation.WitnessNearZero
public import NLA.PF02.UniformPositiveOrientation.PositiveGram

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization Set Filter
open scoped Topology BigOperators

theorem actual_perturbed_orbit_quotient_disconnected {r : ℕ} {η : ℝ}
    (h : regularParameter r η) (hη : 0 ≤ η) (hneg : normalizedWitnessProduct r η < 0) :
    ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (perturbedBlockGram r η) (3+r))) := by
  let g : NLA.PF02.OrbitSpace (perturbedBlockGram r η) (3+r) → Bool :=
    Quot.lift normalizedFiberSign (actual_normalized_fiber_sign_congruent h)
  have hc : Continuous g := continuous_quot_lift (actual_normalized_fiber_sign_congruent h)
    (actual_continuous_normalized_fiber_sign h)
  let Fplus : NLA.PF02.Factorization (perturbedBlockGram r η) (3+r) :=
    ⟨(shiftedFactors (enumeratedFactor r) η,shiftedFactors (enumeratedFactor r) η),
      actual_shifted_factorization r η hη⟩
  let Fminus : NLA.PF02.Factorization (perturbedBlockGram r η) (3+r) :=
    ⟨(shiftedFactors (enumeratedReflectedFactor r) η,shiftedFactors (enumeratedReflectedFactor r) η),
      actual_shifted_reflected_factorization r η hη⟩
  have hneq : normalizedFiberSign Fplus ≠ normalizedFiberSign Fminus := by
    change decide (0 < orientationPolynomial (leadingRows (r := r)
        (normalizedRow (shiftedFactors (enumeratedFactor r) η)))) ≠
      decide (0 < orientationPolynomial (leadingRows (r := r)
        (normalizedRow (shiftedFactors (enumeratedReflectedFactor r) η))))
    rcases mul_neg_iff.mp hneg with ⟨hp,hm⟩ | ⟨hp,hm⟩ <;>
      simp [hp,hm,not_lt_of_gt hp,not_lt_of_gt hm]
  intro hh
  have hi := (hh.image g hc.continuousOn).isPreconnected.subsingleton
  have he : g (Quot.mk _ Fplus) = g (Quot.mk _ Fminus) :=
    hi ⟨Quot.mk _ Fplus,Set.mem_univ _,rfl⟩ ⟨Quot.mk _ Fminus,Set.mem_univ _,rfl⟩
  exact hneq he

theorem actual_positive_perturbed_witness_near_zero (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, 0 < η → η < ε →
      (∀ i j, 0 < perturbedBlockGram r η i j) ∧
      (perturbedBlockGram r η).rank = (3+r)*(3+r+1)/2 ∧
      NLA.PF02.IsPSDRank (perturbedBlockGram r η) (3+r) ∧
      ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (perturbedBlockGram r η) (3+r))) := by
  obtain ⟨a,ha,hA⟩ := actual_regular_parameter_near_zero r
  obtain ⟨b,hb,hB⟩ := actual_normalized_witness_product_negative_near_zero r
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro η hη hεη
  have hreg : regularParameter r η := hA η (by
    rw [abs_of_pos hη]; exact lt_of_lt_of_le hεη (min_le_left _ _))
  have hn : normalizedWitnessProduct r η < 0 :=
    hB η hη.le (lt_of_lt_of_le hεη (min_le_right _ _))
  exact ⟨actual_perturbed_gram_entries_positive r η hη,hreg.1,
    actual_perturbed_psd_rank hreg hη.le,actual_perturbed_orbit_quotient_disconnected hreg hη.le hn⟩

#print axioms actual_perturbed_orbit_quotient_disconnected
#print axioms actual_positive_perturbed_witness_near_zero
end Reference.PF02UniformPositiveOrientation
