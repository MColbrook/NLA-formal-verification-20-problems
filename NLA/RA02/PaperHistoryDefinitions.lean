module

public import NLA.RA02.PaperPivotDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

def AllSquareMinorsNonzero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ s : ℕ, s ≤ n → ∀ rows cols : Fin s ↪ Fin n, (A.submatrix rows cols).det ≠ 0

def historyPrefix {n k s : ℕ} (h : Fin k ↪ Fin n) (hs : s ≤ k) : Fin s ↪ Fin n where
  toFun i := h (Fin.castLE hs i)
  inj' := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin k => x.val) (h.injective hij))

end NLA.RA02.Paper
