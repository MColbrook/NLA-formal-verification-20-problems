module

public import NLA.MD06.CubicConfiguration.CanonicalPairing

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PairingCounts
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

def conjugatePartner {n : ℕ} (τ σ : Equiv.Perm (Dart n)) : Equiv.Perm (Dart n) :=
  τ.symm.trans (σ.trans τ)

noncomputable def relabelPairing {n : ℕ} (τ : Equiv.Perm (Dart n)) (p : Pairing n) :
    Pairing n :=
  ⟨conjugatePartner τ p.val, by
    constructor
    · intro x
      simp only [conjugatePartner, Equiv.trans_apply, Equiv.symm_apply_apply]
      rw [p.property.1]
      exact τ.apply_symm_apply x
    · intro x hx
      have h := congrArg τ.symm hx
      simp only [conjugatePartner, Equiv.trans_apply, Equiv.symm_apply_apply] at h
      exact p.property.2 (τ.symm x) h⟩

noncomputable def pairingRelabelEquiv {n : ℕ} (τ : Equiv.Perm (Dart n)) :
    Pairing n ≃ Pairing n where
  toFun := relabelPairing τ
  invFun := relabelPairing τ.symm
  left_inv := by
    intro p
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp only [relabelPairing, conjugatePartner, Equiv.trans_apply,
      Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv := by
    intro p
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp only [relabelPairing, conjugatePartner, Equiv.trans_apply,
      Equiv.symm_symm, Equiv.apply_symm_apply]

#print axioms relabelPairing
#print axioms pairingRelabelEquiv
end Reference.MD06PairingCounts