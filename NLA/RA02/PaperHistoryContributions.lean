module

public import NLA.RA02.PaperTerminalResidual
public import NLA.RA02.PaperPivotProduct
public import NLA.RA02.PaperLUMass

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem exists_unused_label {n k : ℕ} (hk : k < n) (h : Fin k ↪ Fin n) :
    ∃ p : Fin n, p ∉ Set.range h := by
  have hn : ¬Function.Surjective h := by
    intro hs
    have hc := Fintype.card_le_of_surjective h hs
    simp only [Fintype.card_fin] at hc
    omega
  exact not_forall.mp hn

theorem cholesky_terminal_contribution {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : AllSquareMinorsNonzero A) (h : Fin k ↪ Fin (k+1))
    (htrace : ∀ s : Fin (List.ofFn h).length,
      NLA.RA02.realTrace (NLA.RA02.pathResidual (complexify A) ((List.ofFn h).take s.val)) ≠ 0) :
    NLA.RA02.pathContribution (complexify A) (List.ofFn h) =
      A.det / NLA.RA02.prefixTraceProduct (complexify A) (List.ofFn h) := by
  obtain ⟨p,hp⟩ := exists_unused_label (Nat.lt_succ_self k) h
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k (Nat.le_succ k) h h))
  rw [NLA.RA02.pathContribution, cholesky_pathWeight_det A hA (Nat.le_succ k) h htrace,
    choleskyPath_distinct A hA (Nat.le_succ k) h, complexify_real_trace]
  rw [div_mul_eq_mul_div, terminal_trace_det A h p hp hu]

theorem lu_terminal_contribution {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : AllSquareMinorsNonzero A) (rows cols : Fin k ↪ Fin (k+1)) :
    NLA.RA03.historyMass (complexify A) (fun i => some (rows i,cols i)) *
      NLA.RA03.frobeniusSq (NLA.RA03.historyResidual (complexify A) (fun i => some (rows i,cols i))) =
      A.det^2 / luNormalizerProduct A (List.ofFn (fun i => some (rows i,cols i))) := by
  obtain ⟨p,hp⟩ := exists_unused_label (Nat.lt_succ_self k) rows
  obtain ⟨q,hq⟩ := exists_unused_label (Nat.lt_succ_self k) cols
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k (Nat.le_succ k) rows cols))
  rw [actual_luMass_det A hA (Nat.le_succ k) rows cols,
    luPath_distinct A hA (Nat.le_succ k) rows cols, complexify_frobenius,
    div_mul_eq_mul_div, terminal_frobenius_det A rows cols p q hp hq hu]

#print axioms lu_terminal_contribution
end NLA.RA02.Paper
