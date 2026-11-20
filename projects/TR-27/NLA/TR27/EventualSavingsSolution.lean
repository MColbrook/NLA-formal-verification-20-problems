module

public import NLA.TR27.PaperEventualSavings

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical TensorProduct LinearAlgebra.Projectivization
open Filter
namespace NLA.TR27.Paper

theorem paper_primitive_root_enumeration {L : ℕ} (hL : 0 < L) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ L) :
    Function.Injective (fun a : Fin L => ζ^a.val) ∧
      Set.range (fun a : Fin L => ζ^a.val) = {z : ℂ | z^L = 1} := by
  exact primitive_root_enumeration hL hζ

theorem paper_quotient_difference_tensor_root_average (D r k : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (k*(D-1)+1)) :
    ((k*(D-1)+1 : ℕ) : ℂ)⁻¹ •
      (∑ a : Fin (k*(D-1)+1), ((ζ^a.val)^k)⁻¹ • PiTensorProduct.tprod ℂ
        (fun _ : Fin k => quotientCurve D r (chosenParameters r) (some (ζ^a.val)) -
          quotientCurve D r (chosenParameters r) (some 0))) =
      PiTensorProduct.tprod ℂ (fun _ : Fin k => quotientTangent D r (chosenParameters r)) := by
  exact quotient_difference_tensor_root_average D r k hζ

theorem paper_quotient_tangent_power_upper (D r : ℕ) (hD : 1 ≤ D) (hgap : 1+r < D)
    (hv : quotientTangent D r (chosenParameters r) ≠ 0) (k : ℕ) :
    ProjectiveRankAtMost (productPoints (quotientPoints D r (chosenParameters r)) k)
      ((k*(D-1)+1)*2^k) (powerPoint (Projectivization.mk ℂ _ hv) k) := by
  exact quotient_tangent_power_upper D r hD hgap hv k

theorem paper_quotient_tangent_power_rank_upper (D r : ℕ) (hD : 1 ≤ D) (hgap : 1+r < D)
    (hv : quotientTangent D r (chosenParameters r) ≠ 0) (k : ℕ) :
    projectiveRank (productPoints (quotientPoints D r (chosenParameters r)) k)
      (powerPoint (Projectivization.mk ℂ _ hv) k) ≤ (k*(D-1)+1)*2^k := by
  exact quotient_tangent_power_rank_upper D r hD hgap hv k

theorem paper_quotient_tangent_eventual_saving (D r : ℕ) (hD : 1 ≤ D) (hr : 2 < r)
    (hgap : 1+r < D) (hv : quotientTangent D r (chosenParameters r) ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      projectiveRank (productPoints (quotientPoints D r (chosenParameters r)) k)
        (powerPoint (Projectivization.mk ℂ _ hv) k) < r^k := by
  exact quotient_tangent_eventual_saving D r hD hr hgap hv

theorem paper_family_eventual_saving (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ∃ hv : quotientTangent (familyDegree r m) r (chosenParameters r) ≠ 0,
      (∀ k : ℕ, ProjectiveRankAtMost
        (productPoints (quotientPoints (familyDegree r m) r (chosenParameters r)) k)
        ((k*(familyDegree r m-1)+1)*2^k) (powerPoint (Projectivization.mk ℂ _ hv) k)) ∧
      (∀ᶠ k : ℕ in atTop,
        projectiveRank (productPoints (quotientPoints (familyDegree r m) r (chosenParameters r)) k)
          (powerPoint (Projectivization.mk ℂ _ hv) k) < r^k) := by
  exact family_eventual_saving r m hr hm

theorem paper_explicit_thirteenth_power_saving :
    ∃ hv : quotientTangent 12 3 (chosenParameters 3) ≠ 0,
      projectiveRank (productPoints (quotientPoints 12 3 (chosenParameters 3)) 13)
        (powerPoint (Projectivization.mk ℂ _ hv) 13) ≤ 144*2^13 ∧
      projectiveRank (productPoints (quotientPoints 12 3 (chosenParameters 3)) 13)
        (powerPoint (Projectivization.mk ℂ _ hv) 13) < 3^13 := by
  exact explicit_thirteenth_power_saving

theorem paper_savings_delay_unbounded (N : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ N ≤ m ∧
      ∃ hv : quotientTangent (familyDegree 3 m) 3 (chosenParameters 3) ≠ 0,
        (∀ k : ℕ, 1 ≤ k → k ≤ N →
          projectiveRank (productPoints (quotientPoints (familyDegree 3 m) 3 (chosenParameters 3)) k)
            (powerPoint (Projectivization.mk ℂ _ hv) k) = 3^k) ∧
        (∀ᶠ k : ℕ in atTop,
          projectiveRank (productPoints (quotientPoints (familyDegree 3 m) 3 (chosenParameters 3)) k)
            (powerPoint (Projectivization.mk ℂ _ hv) k) < 3^k) := by
  exact savings_delay_unbounded N

#print axioms paper_primitive_root_enumeration
#print axioms paper_quotient_difference_tensor_root_average
#print axioms paper_quotient_tangent_power_upper
#print axioms paper_quotient_tangent_power_rank_upper
#print axioms paper_quotient_tangent_eventual_saving
#print axioms paper_family_eventual_saving
#print axioms paper_explicit_thirteenth_power_saving
#print axioms paper_savings_delay_unbounded

end NLA.TR27.Paper
