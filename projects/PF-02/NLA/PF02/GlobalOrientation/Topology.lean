module

public import NLA.PF02.GlobalOrientation.GeneralCongruence
public import NLA.PF02.GlobalOrientation.WitnessOrientation
public import NLA.PF02.GlobalOrientation.SignDefinitions
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix Reference.PF02BlockConstruction Set Filter
open scoped Topology

theorem continuous_orientation_polynomial (k : ℕ) :
    Continuous (orientationPolynomial (k := k)) := by
  unfold orientationPolynomial coordinateRows
  fun_prop

theorem continuous_actual_fiber_sign (r : ℕ) : Continuous (fiberSign (r := r)) := by
  have hc : Continuous (fun F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r) =>
      orientationPolynomial (leadingRows F.val.1)) := by
    apply (continuous_orientation_polynomial (3+r)).comp
    unfold leadingRows Reference.PF02BlockSupportRecovery.blockRows
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro F
  by_cases hp : 0 < orientationPolynomial (leadingRows F.val.1)
  · have he : ∀ᶠ G in 𝓝 F, 0 < orientationPolynomial (leadingRows G.val.1) :=
      (isOpen_lt continuous_const hc).mem_nhds hp
    apply (continuousAt_const (y := true)).congr_of_eventuallyEq
    exact he.mono (fun G hG => by simp [fiberSign,hG])
  · have hn : orientationPolynomial (leadingRows F.val.1) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hp) (actual_orientation_polynomial_ne_zero F)
    have he : ∀ᶠ G in 𝓝 F, orientationPolynomial (leadingRows G.val.1) < 0 :=
      (isOpen_lt hc continuous_const).mem_nhds hn
    apply (continuousAt_const (y := false)).congr_of_eventuallyEq
    exact he.mono (fun G hG => by simp [fiberSign,not_lt_of_gt hG])

theorem actual_fiber_sign_congruent {r : ℕ}
    (F G : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) (h : NLA.PF02.Congruent F G) :
    fiberSign F = fiberSign G := by
  obtain ⟨S,hrow,_⟩ := h
  have hS : (S : Matrix (Fin (3+r)) (Fin (3+r)) ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp S.isUnit).ne_zero
  have hG : leadingRows G.val.1 = fun p => (S : Matrix (Fin (3+r)) (Fin (3+r)) ℝ).transpose *
      leadingRows F.val.1 p * S := by
    funext p
    exact hrow (Fintype.equivFin (BlockIndex r) (Sum.inl p))
  have hp := actual_invertible_orientation_product_pos F S hS
  rw [← hG] at hp
  rcases mul_pos_iff.mp hp with ⟨hf,hg⟩ | ⟨hf,hg⟩
  · simp [fiberSign,hf,hg]
  · simp [fiberSign,not_lt_of_gt hf,not_lt_of_gt hg]

theorem actual_all_size_orbit_quotient_disconnected (r : ℕ) :
    ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (enumeratedRealGram r) (3+r))) := by
  let g : NLA.PF02.OrbitSpace (enumeratedRealGram r) (3+r) → Bool :=
    Quot.lift fiberSign actual_fiber_sign_congruent
  have hc : Continuous g := continuous_quot_lift actual_fiber_sign_congruent (continuous_actual_fiber_sign r)
  let Fplus : NLA.PF02.Factorization (enumeratedRealGram r) (3+r) :=
    ⟨(enumeratedFactor r,enumeratedFactor r), enumerated_factorization r⟩
  let Fminus : NLA.PF02.Factorization (enumeratedRealGram r) (3+r) :=
    ⟨(enumeratedReflectedFactor r,enumeratedReflectedFactor r), enumerated_reflected_factorization r⟩
  have hn := actual_witness_orientation_product_negative r
  have hneq : fiberSign Fplus ≠ fiberSign Fminus := by
    change decide (0 < orientationPolynomial (leadingRows (enumeratedFactor r))) ≠
      decide (0 < orientationPolynomial (leadingRows (enumeratedReflectedFactor r)))
    rcases mul_neg_iff.mp hn with ⟨hp,hm⟩ | ⟨hp,hm⟩ <;>
      simp [hp,hm,not_lt_of_gt hp,not_lt_of_gt hm]
  intro h
  have hi := (h.image g hc.continuousOn).isPreconnected.subsingleton
  have he : g (Quot.mk _ Fplus) = g (Quot.mk _ Fminus) :=
    hi ⟨Quot.mk _ Fplus,Set.mem_univ _,rfl⟩ ⟨Quot.mk _ Fminus,Set.mem_univ _,rfl⟩
  exact hneq he

#print axioms continuous_orientation_polynomial
#print axioms continuous_actual_fiber_sign
#print axioms actual_fiber_sign_congruent
#print axioms actual_all_size_orbit_quotient_disconnected
end Reference.PF02GlobalOrientation
