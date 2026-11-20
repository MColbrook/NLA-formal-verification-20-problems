module

public import NLA.TR27.PaperTensorRootFilter
public import NLA.TR27.PaperProjectedBorder

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical TensorProduct
namespace NLA.TR27.Paper

/-- The finite list used in the average enumerates every L-th root exactly once. -/
theorem primitive_root_enumeration {L : ℕ} (hL : 0 < L) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ L) :
    Function.Injective (fun a : Fin L => ζ^a.val) ∧
      Set.range (fun a : Fin L => ζ^a.val) = {z : ℂ | z^L = 1} := by
  letI : NeZero L := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact Fin.ext (hζ.pow_inj a.isLt b.isLt hab)
  · ext z
    constructor
    · rintro ⟨a, rfl⟩
      change (ζ^a.val)^L = 1
      rw [← pow_mul, Nat.mul_comm a.val L, pow_mul, hζ.pow_eq_one, one_pow]
    · intro hz
      obtain ⟨a, ha, he⟩ := hζ.eq_pow_of_pow_eq_one hz
      exact ⟨⟨a,ha⟩,he⟩

theorem secantSlope_polynomial (D : ℕ) (t : ℂ) :
    secantSlope D t = ∑ j : Fin D, t^j.val •
      (Pi.single j.succ 1 : CurveSpace D) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [secantSlope]
  · simp [secantSlope, Pi.single_apply]

theorem projectedSecant_polynomial (D r : ℕ) (t : ℂ) :
    projectedSecant D r t = ∑ j : Fin D, t^j.val •
      quotientProjection D r (chosenParameters r) (Pi.single j.succ 1) := by
  rw [projectedSecant, secantSlope_polynomial, map_sum]
  simp only [map_smul]

theorem projectedSecant_tensor_root_average (D r k : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (k*(D-1)+1)) :
    ((k*(D-1)+1 : ℕ) : ℂ)⁻¹ •
      (∑ a : Fin (k*(D-1)+1), PiTensorProduct.tprod ℂ
        (fun _ : Fin k => projectedSecant D r (ζ^a.val))) =
      PiTensorProduct.tprod ℂ (fun _ : Fin k => quotientTangent D r (chosenParameters r)) := by
  simpa only [← projectedSecant_polynomial, projectedSecant_zero] using
    polynomial_tensor_root_average D k
      (fun j => quotientProjection D r (chosenParameters r) (Pi.single j.succ 1)) hζ

/-- The literal weighted coefficient formula for q(t)=pi(c(t)-c(0)). -/
theorem quotient_difference_tensor_root_average (D r k : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (k*(D-1)+1)) :
    ((k*(D-1)+1 : ℕ) : ℂ)⁻¹ •
      (∑ a : Fin (k*(D-1)+1), ((ζ^a.val)^k)⁻¹ • PiTensorProduct.tprod ℂ
        (fun _ : Fin k => quotientCurve D r (chosenParameters r) (some (ζ^a.val)) -
          quotientCurve D r (chosenParameters r) (some 0))) =
      PiTensorProduct.tprod ℂ (fun _ : Fin k => quotientTangent D r (chosenParameters r)) := by
  rw [← projectedSecant_tensor_root_average D r k hζ]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [projectedSecant_difference D r _ (pow_ne_zero _ (hζ.ne_zero (by omega)))]
  rw [MultilinearMap.map_smul_univ]
  simp

#print axioms quotient_difference_tensor_root_average
end NLA.TR27.Paper
