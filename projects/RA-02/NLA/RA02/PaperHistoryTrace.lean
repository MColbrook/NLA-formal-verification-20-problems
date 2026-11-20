module

public import NLA.RA02.PaperHistoryContributions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

theorem take_history {n k s : ℕ} (h : Fin k ↪ Fin n) (hs : s ≤ k) :
    (List.ofFn h).take s = List.ofFn (historyPrefix h hs) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hs]
  · intro i hi hj
    simp [historyPrefix]

theorem interpolatoryResidual_nonzero {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k < n) (rows cols : Fin k ↪ Fin n) :
    interpolatoryResidual A rows cols ≠ 0 := by
  obtain ⟨p,hp⟩ := exists_unused_label hk rows
  obtain ⟨q,hq⟩ := exists_unused_label hk cols
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k hk.le rows cols))
  have ha := hA (k+1) hk (appendEmbedding rows p hp) (appendEmbedding cols q hq)
  rw [residual_bordered_determinant A rows cols p q hp hq hu] at ha
  intro hzero
  have hz := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M p q) hzero
  exact (mul_ne_zero_iff.mp ha).2 hz

theorem cholesky_distinct_prefix_trace {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hpsd : (complexify A).PosSemidef)
    (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    ∀ s : Fin (List.ofFn h).length,
      NLA.RA02.realTrace (NLA.RA02.pathResidual (complexify A) ((List.ofFn h).take s.val)) ≠ 0 := by
  intro s
  have hs : s.val < k := by simpa using s.isLt
  have hsn : s.val < n := lt_of_lt_of_le hs hk
  have hp := NLA.RA02.pathResidual_posSemidef (complexify A) hpsd ((List.ofFn h).take s.val)
  apply ne_of_gt (NLA.RA02.realTrace_pos hp ?_)
  rw [take_history h hs.le, choleskyPath_distinct A hA hsn.le (historyPrefix h hs.le)]
  exact (complexify_eq_zero _).not.mpr
    (interpolatoryResidual_nonzero A hA hsn (historyPrefix h hs.le) (historyPrefix h hs.le))

theorem cholesky_terminal_contribution_psd {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : AllSquareMinorsNonzero A) (hpsd : (complexify A).PosSemidef)
    (h : Fin k ↪ Fin (k+1)) :
    NLA.RA02.pathContribution (complexify A) (List.ofFn h) =
      A.det / NLA.RA02.prefixTraceProduct (complexify A) (List.ofFn h) :=
  cholesky_terminal_contribution A hA h (cholesky_distinct_prefix_trace A hA hpsd (Nat.le_succ k) h)

#print axioms cholesky_terminal_contribution_psd
end NLA.RA02.Paper
