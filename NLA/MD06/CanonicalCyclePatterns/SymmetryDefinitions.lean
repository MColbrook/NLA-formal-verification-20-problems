module

public import NLA.MD06.CanonicalCyclePatterns.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CyclePairPatterns

def RotatedCycle {n ell : ℕ} (D : CycleData n ell) (s : Fin ell) : CycleData n ell :=
  (⟨fun i => D.1 (finCycle s i),
    fun _ _ h => (finCycle s).injective (D.1.injective h)⟩,
   fun i => D.2 (finCycle s i))

def ReflectedCycle {n ell : ℕ} [NeZero ell] (D : CycleData n ell) : CycleData n ell :=
  (⟨fun i => D.1 (-i),
    fun _ _ h => neg_injective (D.1.injective h)⟩,
   fun i => ⟨((D.2 (-i)).val.2,(D.2 (-i)).val.1),((D.2 (-i)).property).symm⟩)

def SymmetryCycle {n ell : ℕ} [NeZero ell] (D : CycleData n ell)
    (z : Fin ell × Bool) : CycleData n ell :=
  if z.2 then RotatedCycle D z.1 else ReflectedCycle (RotatedCycle D z.1)

end Reference.MD06CanonicalCyclePatterns
