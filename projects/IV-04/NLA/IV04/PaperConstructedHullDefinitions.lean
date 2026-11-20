module

public import NLA.IV04.PaperConstructedBoxDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper

def positiveCornerRhs (n : ℕ) (hn : 0 < n) : Fin n → ℝ :=
  Pi.single ⟨n-1,Nat.sub_lt hn (by decide)⟩ (-1)
def positiveSolutions (n : ℕ) (hn : 0 < n) (S : Set (Mat n)) : Set (Fin n → ℝ) :=
  {x | ∃ A ∈ S, A.mulVec x=positiveCornerRhs n hn}
def positiveFirstCoordinates (n : ℕ) (hn : 0 < n) (S : Set (Mat n)) : Set ℝ :=
  (fun x : Fin n → ℝ => x ⟨0,hn⟩) '' positiveSolutions n hn S

namespace IntegerPartition

def constructedSolutions (P : IntegerPartition) : Set (Fin P.layerCount → ℝ) :=
  positiveSolutions P.layerCount (by have := P.nonempty; dsimp [layerCount]; omega)
    P.intervalBox.realizations
def constructedFirstCoordinates (P : IntegerPartition) : Set ℝ :=
  positiveFirstCoordinates P.layerCount (by have := P.nonempty; dsimp [layerCount]; omega)
    P.intervalBox.realizations

end IntegerPartition
end IV04.Paper
