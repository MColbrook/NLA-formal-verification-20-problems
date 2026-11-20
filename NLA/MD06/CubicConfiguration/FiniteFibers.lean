module

public import NLA.MD06.CubicConfiguration.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration
open Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_constant_fiber_total {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (f : Ω → Λ) (C : ℕ) (hf : ∀ y : Λ, Fintype.card {x : Ω // f x = y} = C) :
    Fintype.card Ω = Fintype.card Λ * C := by
  let e : (Σ y : Λ, {x : Ω // f x = y}) ≃ Ω :=
    { toFun := fun p => p.2.val
      invFun := fun x => ⟨f x,⟨x,rfl⟩⟩
      left_inv := by rintro ⟨y,x,h⟩; subst y; rfl
      right_inv := by intro x; rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp [hf]

theorem actual_constant_fiber_event {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (f : Ω → Λ) (C : ℕ) (hf : ∀ y : Λ, Fintype.card {x : Ω // f x = y} = C)
    (P : Λ → Prop) :
    Fintype.card {x : Ω // P (f x)} = Fintype.card {y : Λ // P y} * C := by
  let e : (Σ y : {y : Λ // P y}, {x : Ω // f x = y.val}) ≃
      {x : Ω // P (f x)} :=
    { toFun := fun p => ⟨p.2.val, by rw [p.2.property]; exact p.1.property⟩
      invFun := fun x => ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
      left_inv := by rintro ⟨⟨y,hy⟩,⟨x,hx⟩⟩; change f x = y at hx; subst y; rfl
      right_inv := by intro x; rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp [hf]

theorem actual_constant_fiber_probability {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (f : Ω → Λ) (C : ℕ) (hf : ∀ y : Λ, Fintype.card {x : Ω // f x = y} = C)
    (hC : 0 < C) (P : Λ → Prop) :
    countingProbability (fun x : Ω => P (f x)) = countingProbability P := by
  unfold countingProbability
  rw [actual_constant_fiber_event f C hf P, actual_constant_fiber_total f C hf]
  simp only [Nat.cast_mul]
  have hc : (C : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hC
  exact mul_div_mul_right _ _ hc

#print axioms actual_constant_fiber_total
#print axioms actual_constant_fiber_event
#print axioms actual_constant_fiber_probability
end Reference.MD06CubicConfiguration
