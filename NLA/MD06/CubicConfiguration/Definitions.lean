module

public import NLA.MD06.FiniteProbability.Definitions
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration
open Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Dart (n : ℕ) := Fin n × Fin 3

abbrev Pairing (n : ℕ) :=
  {σ : Equiv.Perm (Dart n) // Function.Involutive σ ∧ ∀ x, σ x ≠ x}

noncomputable instance pairingFintype (n : ℕ) : Fintype (Pairing n) := Fintype.ofFinite _

def IsSimplePairing {n : ℕ} (p : Pairing n) : Prop :=
  (∀ u : Fin n, ∀ a : Fin 3, (p.val (u,a)).fst ≠ u) ∧
    ∀ u : Fin n, Function.Injective (fun a : Fin 3 => (p.val (u,a)).fst)

abbrev SimpleConfiguration (n : ℕ) := {p : Pairing n // IsSimplePairing p}

noncomputable instance configurationFintype (n : ℕ) :
    Fintype (SimpleConfiguration n) := Fintype.ofFinite _

noncomputable def configurationGraph {n : ℕ} (p : SimpleConfiguration n) :
    SimpleGraph (Fin n) where
  Adj u v := ∃ a : Fin 3, (p.val.val (u,a)).fst = v
  symm := by
    constructor
    intro u v h
    obtain ⟨a,ha⟩ := h
    refine ⟨(p.val.val (u,a)).snd, ?_⟩
    have heq : (v,(p.val.val (u,a)).snd) = p.val.val (u,a) :=
      Prod.ext ha.symm rfl
    rw [heq]
    exact congrArg Prod.fst (p.val.property.1 (u,a))
  loopless := by
    constructor
    intro u h
    obtain ⟨a,ha⟩ := h
    exact p.property.1 u a ha

abbrev NeighborFrames {n : ℕ} (G : SimpleGraph (Fin n)) :=
  ∀ u : Fin n, Fin 3 ≃ G.neighborSet u

end Reference.MD06CubicConfiguration
