module

/- Explicit ascending original-index scans and inverse lookup; no choice of enumeration.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Card

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedIndex

def indexList {m : ℕ} (p : Fin m → Prop) [DecidablePred p] : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (p i))

theorem mem_indexList {m : ℕ} (p : Fin m → Prop) [DecidablePred p] (i : Fin m) :
    i∈indexList p ↔ p i := by simp [indexList]

theorem nodup_indexList {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    (indexList p).Nodup := (List.nodup_finRange m).filter _

def predicateListEquiv {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    {i : Fin m // p i} ≃ {i : Fin m // i∈indexList p} where
  toFun i := ⟨i.val,(mem_indexList p i.val).mpr i.property⟩
  invFun i := ⟨i.val,(mem_indexList p i.val).mp i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def listEnum {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    {i : Fin m // p i} ≃ Fin (indexList p).length :=
  (predicateListEquiv p).trans (List.Nodup.getEquiv (indexList p) (nodup_indexList p)).symm

theorem indexList_length {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    (indexList p).length=Fintype.card {i : Fin m // p i} := by
  have h:=Fintype.card_congr (listEnum p)
  simpa only [Fintype.card_fin] using h.symm

def indexEnum {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    {i : Fin m // p i} ≃ Fin (Fintype.card {i : Fin m // p i}) :=
  (listEnum p).trans (finCongr (indexList_length p))

theorem indexEnum_inverse_lookup {m : ℕ} (p : Fin m → Prop) [DecidablePred p]
    (j : Fin (Fintype.card {i : Fin m // p i})) :
    ((indexEnum p).symm j).val=(indexList p).get ((finCongr (indexList_length p)).symm j) := rfl

theorem indexEnum_forward_lookup {m : ℕ} (p : Fin m → Prop) [DecidablePred p]
    (i : {i : Fin m // p i}) : (indexEnum p i).val=(indexList p).idxOf i.val := rfl

end Reference.LexOrderedIndex
