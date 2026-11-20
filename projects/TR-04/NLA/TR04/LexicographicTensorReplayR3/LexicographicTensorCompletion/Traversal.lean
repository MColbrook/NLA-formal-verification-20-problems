module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Explicit row-major and mixed-radix traversal equations; no chosen permutations. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorCompletion.Layout
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section

theorem lexIndex_cons_value (n : ℕ) (ns : List ℕ) (i : Fin n) (j : ModeIndex ns) :
    (lexIndex (n::ns) (i,j)).val=(lexIndex ns j).val+lexCard ns*i.val := rfl

theorem concreteLayout_cons_value (n : ℕ) (ns : List ℕ) (i : Fin n) (j : ModeIndex ns) :
    (concreteLayout (n::ns) (i,j)).val=(concreteLayout ns j).val+lexCard ns*i.val := rfl

theorem concreteRow_forward (m n : ℕ) (i : Fin m) (j : Fin n) :
    (rowEquiv m n (i,j)).val=j.val+n*i.val := rfl

theorem concreteRow_inverse_fst (m n : ℕ) (i : Fin (rowCount m n)) :
    ((rowEquiv m n).symm i).1.val=i.val/n := rfl

theorem concreteRow_inverse_snd (m n : ℕ) (i : Fin (rowCount m n)) :
    ((rowEquiv m n).symm i).2.val=i.val%n := rfl

#print axioms lexIndex_cons_value
#print axioms concreteLayout_cons_value
#print axioms concreteRow_forward
#print axioms concreteRow_inverse_fst
#print axioms concreteRow_inverse_snd
end
end Reference.LexTensorCompletion
