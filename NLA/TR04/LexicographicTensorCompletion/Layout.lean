module

/- Literal mixed-radix lexicographic column traversal. -/
public import NLA.TR04.LexicographicTensorCompletion.Definitions
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Card

@[expose] public section
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
def lexCard : List ℕ → ℕ
  | [] => 1
  | n::ns => n*lexCard ns
def lexIndex : (ns : List ℕ) → ModeIndex ns ≃ Fin (lexCard ns)
  | [] => {
      toFun := fun _ => ⟨0,by change 0<1; omega⟩
      invFun := fun _ => PUnit.unit
      left_inv := fun i => by cases i; rfl
      right_inv := fun j => by apply Fin.ext; change 0=j.val; have hj:=j.isLt; change j.val<1 at hj; omega }
  | n::ns => (Equiv.prodCongr (Equiv.refl (Fin n)) (lexIndex ns)).trans finProdFinEquiv
theorem lexCard_eq_card (ns : List ℕ) : lexCard ns=Fintype.card (ModeIndex ns) := by
  induction ns with
  | nil => change 1=Fintype.card PUnit; exact Fintype.card_punit.symm
  | cons n ns ih =>
      change n*lexCard ns=Fintype.card (Fin n × ModeIndex ns)
      rw [Fintype.card_prod,Fintype.card_fin,ih]
def concreteLayout (ns : List ℕ) : ModeIndex ns ≃ Fin (Fintype.card (ModeIndex ns)) :=
  (lexIndex ns).trans (finCongr (lexCard_eq_card ns))
end
end Reference.LexTensorCompletion
