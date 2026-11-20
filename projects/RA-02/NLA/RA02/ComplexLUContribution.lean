module

public import NLA.RA02.ComplexLUMass
public import NLA.RA02.ComplexHistoryTerminal
public import NLA.RA02.PaperHistoryContributions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper.ComplexHistory

theorem lu_terminal_contribution {k : ℕ} (A : NLA.RA02.Square (k+1))
    (hA : AllSquareMinorsNonzero A) (rows cols : Fin k ↪ Fin (k+1)) :
    NLA.RA03.historyMass A (fun i => some (rows i,cols i)) *
      NLA.RA03.frobeniusSq (NLA.RA03.historyResidual A (fun i => some (rows i,cols i))) =
      Complex.normSq A.det / luNormalizerProduct A (List.ofFn (fun i => some (rows i,cols i))) := by
  obtain ⟨p,hp⟩ := exists_unused_label (Nat.lt_succ_self k) rows
  obtain ⟨q,hq⟩ := exists_unused_label (Nat.lt_succ_self k) cols
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k (Nat.le_succ k) rows cols))
  rw [actual_luMass_det A hA (Nat.le_succ k) rows cols,
    luPath_distinct A hA (Nat.le_succ k) rows cols,
    div_mul_eq_mul_div, terminal_frobenius_det A rows cols p q hp hq hu]

end NLA.RA02.Paper.ComplexHistory
