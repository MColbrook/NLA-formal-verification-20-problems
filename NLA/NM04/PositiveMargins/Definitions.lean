module

/-
Arbitrary positive-margin extension of Colbrook's NM-04 manuscript.
Development source: mathematical authorship remains with the paper authors;
OpenAI Codex assists with formalization. Statement definitions only.
-/
public import NLA.NM04.Definitions

@[expose] public section

set_option autoImplicit false

namespace NLA.NM04.PositiveMargins
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v

def exchangeColumn {α : Type u} {β : Type v} [DecidableEq β]
    (I : MinorIndex α β) (s : I.1.2) (t : {t : β // t ∉ I.1.2}) : MinorIndex α β :=
  ⟨(I.1.1, insert t.val (I.1.2.erase s.val)), by
    have ht : t.val ∉ I.1.2.erase s.val := fun h => t.property (Finset.mem_of_mem_erase h)
    have hc : 1 ≤ I.1.2.card := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨s.val, s.property⟩)
    rw [Finset.card_insert_of_notMem ht, Finset.card_erase_of_mem s.property,
      Nat.sub_add_cancel hc]
    exact I.property⟩

def swapIndex {α : Type u} {β : Type v} (I : MinorIndex α β) : MinorIndex β α :=
  ⟨(I.1.2, I.1.1), I.property.symm⟩

def exchangeRow {α : Type u} {β : Type v} [DecidableEq α]
    (I : MinorIndex α β) (s : I.1.1) (t : {t : α // t ∉ I.1.1}) : MinorIndex α β :=
  swapIndex (exchangeColumn (swapIndex I) s t)

variable {α : Type u} {β : Type v}
variable [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]

/-- Actual single selected-column cofactor direction. This definition is pure;
its signed Laplace and replacement identities are proved in the solution. -/
def columnForm (T : Matrix α β ℝ) (I : MinorIndex α β) (c : I.1.2)
    (x : α → ℝ) : ℝ :=
  cofactorForm T I (fun r t => if t = (c : β) then x r else 0)

def lower (a : α → ℝ) (b : β → ℝ) (f : MinorIndex α β → ℝ)
    (I : MinorIndex α β) : ℝ :=
  ∑ s : I.1.1, ∑ t : I.1.2,
    (-1 : ℝ) ^ (position (s : α) I.1.1 + position (t : β) I.1.2) *
      (a s * b t) * f (erasedIndex I s t)

def column (b : β → ℝ) (f : MinorIndex α β → ℝ) (I : MinorIndex α β) : ℝ :=
  ∑ s : I.1.2, ∑ t : {t : β // t ∉ I.1.2}, b s *
    (-1 : ℝ) ^ (position (s : β) I.1.2 + position (t : β) (exchangeColumn I s t).1.2) *
      f (exchangeColumn I s t)

def row (a : α → ℝ) (f : MinorIndex α β → ℝ) (I : MinorIndex α β) : ℝ :=
  ∑ s : I.1.1, ∑ t : {t : α // t ∉ I.1.1}, a s *
    (-1 : ℝ) ^ (position (s : α) I.1.1 + position (t : α) (exchangeRow I s t).1.1) *
      f (exchangeRow I s t)

def diagonal (a : α → ℝ) (b : β → ℝ) (τ : ℝ) (I : MinorIndex α β) : ℝ :=
  (∑ s : I.1.1, a s) + (∑ t : I.1.2, b t) - τ

def action (a : α → ℝ) (b : β → ℝ) (τ : ℝ)
    (f : MinorIndex α β → ℝ) (I : MinorIndex α β) : ℝ :=
  diagonal a b τ I * f I + raising f I - lower a b f I + column b f I + row a f I

/-- The literal signed transitions, weighted by their deleted row/column labels.
Each erasure or exchange is enumerated by actual selected and unselected labels.
No minor, inverse or nonzero-minor condition enters this coefficient matrix. -/
def G (a : α → ℝ) (b : β → ℝ) (τ : ℝ) :
    Matrix (MinorIndex α β) (MinorIndex α β) ℝ := fun I J =>
  (if I = J then diagonal a b τ I else 0) + (raisingCoefficient I J : ℝ) -
    (∑ s : I.1.1, ∑ t : I.1.2, if erasedIndex I s t = J then
      (-1 : ℝ) ^ (position (s : α) I.1.1 + position (t : β) I.1.2) * (a s * b t)
      else 0) +
    (∑ s : I.1.2, ∑ t : {t : β // t ∉ I.1.2}, if exchangeColumn I s t = J then
      b s * (-1 : ℝ) ^ (position (s : β) I.1.2 +
        position (t : β) (exchangeColumn I s t).1.2) else 0) +
    (∑ s : I.1.1, ∑ t : {t : α // t ∉ I.1.1}, if exchangeRow I s t = J then
      a s * (-1 : ℝ) ^ (position (s : α) I.1.1 +
        position (t : α) (exchangeRow I s t).1.1) else 0)

def Margins {m n : ℕ} (S : Rect m n) (a : Fin m → ℝ) (b : Fin n → ℝ) : Prop :=
  (∀ i, ∑ j, S i j = a i) ∧ (∀ j, ∑ i, S i j = b j)

def pencil {m n : ℕ} (A : Rect m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (τ z : ℝ) :
    Matrix (Index m n) (Index m n) ℝ :=
  Matrix.diagonal (gamma A hm hn) +
    (z / (a (firstIndex hm) * b (firstIndex hn))) •
      (G (fun i : Tail m => a i.val) (fun j : Tail n => b j.val) τ *
        Matrix.diagonal (delta A hm hn))

end
end NLA.NM04.PositiveMargins
