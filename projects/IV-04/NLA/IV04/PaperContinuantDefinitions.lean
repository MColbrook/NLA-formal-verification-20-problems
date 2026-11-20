module

public import PaperDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace IV04.Paper

def continuantMatrix (n : ℕ) (a β : ℕ → ℝ) : Mat n := fun i j =>
  if i=j then a i.val else if j.val=i.val+1 then 1 else if i.val=j.val+1 then β i.val else 0

def continuantValue (a β : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a 0
  | n+2 => a (n+1)*continuantValue a β (n+1)-β (n+1)*continuantValue a β n

def companion (a β : ℝ) : Mat 2 := !![a,-β;1,0]

def companionProduct (a β : ℕ → ℝ) : ℕ → Mat 2
  | 0 => 1
  | n+1 => companion (a n) (β n)*companionProduct a β n

def companionVector (a β : ℕ → ℝ) (n : ℕ) : Fin 2 → ℝ :=
  (companionProduct a β n).mulVec ![1,0]

end IV04.Paper
