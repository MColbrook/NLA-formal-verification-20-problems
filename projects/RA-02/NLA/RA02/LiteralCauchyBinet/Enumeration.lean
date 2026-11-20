module

public import NLA.RA02.LiteralCauchyBinet.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace RootRA02CauchyBinet
open Finset Function

def enumeratedPermutation {n s : ℕ} (p : SizedSubset n s × Equiv.Perm (Fin s)) :
    Fin s ↪ Fin n :=
  ⟨fun i => enumerate p.1 (p.2 i), (enumerate p.1).injective.comp p.2.injective⟩

theorem enumeratedPermutation_image {n s : ℕ}
    (p : SizedSubset n s × Equiv.Perm (Fin s)) :
    Finset.univ.image (enumeratedPermutation p) = p.1.val := by
  change Finset.univ.image ((enumerate p.1) ∘ p.2) = p.1.val
  rw [← Finset.image_image]
  simp [enumerate]

theorem enumeratedPermutation_bijective (n s : ℕ) :
    Function.Bijective (@enumeratedPermutation n s) := by
  classical
  constructor
  · rintro ⟨T, σ⟩ ⟨U, τ⟩ h
    have hT : T = U := Subtype.ext <| by
      simpa only [enumeratedPermutation_image] using
        congrArg (fun f : Fin s ↪ Fin n => Finset.univ.image f) h
    subst U
    congr 1
    apply Equiv.ext
    intro i
    exact (enumerate T).injective (congrArg (fun f : Fin s ↪ Fin n => f i) h)
  · intro f
    let T : SizedSubset n s := ⟨Finset.univ.image f, by
      rw [Finset.card_image_of_injective _ f.injective]
      simp⟩
    have hm (i : Fin s) : f i ∈ T.val := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    let g : Fin s → Fin s := fun i =>
      (T.val.orderIsoOfFin T.property).symm ⟨f i, hm i⟩
    have hg (i : Fin s) : enumerate T (g i) = f i := by
      change ((T.val.orderIsoOfFin T.property)
        ((T.val.orderIsoOfFin T.property).symm ⟨f i, hm i⟩)).val = f i
      simp
    have hgi : Function.Injective g := by
      intro i j hij
      apply f.injective
      rw [← hg i, ← hg j, hij]
    let σ : Equiv.Perm (Fin s) := Equiv.ofBijective g
      (Finite.injective_iff_bijective.mp hgi)
    refine ⟨(T, σ), ?_⟩
    apply Function.Embedding.ext
    exact hg

end RootRA02CauchyBinet
