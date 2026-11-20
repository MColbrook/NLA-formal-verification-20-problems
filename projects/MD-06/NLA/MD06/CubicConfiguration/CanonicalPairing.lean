module

public import NLA.MD06.CubicConfiguration.UniformDefinitions
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration
open Reference.MD06FiniteProbability

def dartSplit (k : ℕ) :
    Dart (Size k) ≃ Fin 2 × (Fin (k+2) × Fin 3) :=
  (Equiv.prodCongr
    (finProdFinEquiv : Fin 2 × Fin (k+2) ≃ Fin (Size k)).symm
    (Equiv.refl (Fin 3))).trans (Equiv.prodAssoc _ _ _)

def canonicalPartner (k : ℕ) : Equiv.Perm (Dart (Size k)) :=
  (dartSplit k).trans
    ((Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1)
      (Equiv.refl (Fin (k+2) × Fin 3))).trans (dartSplit k).symm)

noncomputable def canonicalPairing (k : ℕ) : Pairing (Size k) :=
  ⟨canonicalPartner k, by
    constructor
    · intro x
      apply (dartSplit k).injective
      simp only [canonicalPartner, Equiv.trans_apply, Equiv.apply_symm_apply,
        Equiv.prodCongr_apply]
      apply Prod.ext
      · have hi (a : Fin 2) : Equiv.swap (0 : Fin 2) 1 (Equiv.swap 0 1 a) = a := by
          fin_cases a <;> decide
        exact hi _
      · rfl
    · intro x hx
      have h := congrArg (fun y => ((dartSplit k) y).fst) hx
      simp only [canonicalPartner, Equiv.trans_apply, Equiv.apply_symm_apply,
        Equiv.prodCongr_apply] at h
      have hn (a : Fin 2) : Equiv.swap (0 : Fin 2) 1 a ≠ a := by
        fin_cases a <;> decide
      exact hn _ h⟩

noncomputable instance rawPairingNonempty (k : ℕ) : Nonempty (Pairing (Size k)) :=
  ⟨canonicalPairing k⟩

noncomputable def UniformPairing (k : ℕ) : PMF (Pairing (Size k)) :=
  PMF.ofFintype (fun _ => (Fintype.card (Pairing (Size k)) : ENNReal)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Pairing (Size k)) ≠ 0))
      (by simp))

end Reference.MD06CubicConfiguration
