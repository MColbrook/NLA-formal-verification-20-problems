module

public import NLA.RA02.PaperPrefixDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
namespace NLA.RA02.Paper

def presentRowColumnEquiv {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    {i : Fin s // (rows i).val < s} ≃ {j : Fin s // Fin.castLE hs j ∈ Set.range rows} where
  toFun i := ⟨⟨(rows i.val).val, i.property⟩, ⟨i.val, Fin.ext rfl⟩⟩
  invFun j := ⟨Classical.choose j.property, by
    have h := congrArg Fin.val (Classical.choose_spec j.property)
    change (rows (Classical.choose j.property)).val = j.val.val at h
    rw [h]
    exact j.val.isLt⟩
  left_inv i := by
    apply Subtype.ext
    apply rows.injective
    exact Classical.choose_spec (show Fin.castLE hs ⟨(rows i.val).val,i.property⟩ ∈
      Set.range rows from ⟨i.val,Fin.ext rfl⟩)
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    change (rows (Classical.choose j.property)).val = j.val.val
    exact congrArg Fin.val (Classical.choose_spec j.property)

theorem missingColumn_card_eq_outsideRow {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    Fintype.card (MissingColumn hs rows) = Fintype.card (OutsideRow rows) := by
  have h := Fintype.card_congr (presentRowColumnEquiv hs rows)
  have hi := Fintype.card_subtype_compl (fun i : Fin s => (rows i).val < s)
  have hj := Fintype.card_subtype_compl (fun j : Fin s => Fin.castLE hs j ∈ Set.range rows)
  simp only [not_lt] at hi
  change Fintype.card (OutsideRow rows) = Fintype.card (Fin s) - _ at hi
  change Fintype.card (MissingColumn hs rows) = Fintype.card (Fin s) - _ at hj
  omega

end NLA.RA02.Paper
