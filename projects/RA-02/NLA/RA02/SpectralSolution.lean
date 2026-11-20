module

public import NLA.RA02.PaperSpectralConclusions
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Topology
open Filter
namespace NLA.RA02.Paper

theorem paper_sharp_family (n : ℕ) (t : ℝ) :
    sharpFamily n t = lower n t * Matrix.diagonal (fun i : Fin n => (t^(n^2))^i.val) *
      (lower n t).transpose := by
  rfl

theorem paper_sharp_positive_definite (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (sharpFamily n t).PosDef := by
  exact sharpFamily_posDef n t ht

theorem paper_sharp_positive_entries (n : ℕ) (t : ℝ) (ht : 0 < t) (i j : Fin (n+1)) :
    0 < sharpFamily (n+1) t i j := by
  exact sharpFamily_entry_pos n t ht i j

theorem paper_lower_determinant (n : ℕ) (t : ℝ) : (lower n t).det = 1 := by
  exact lower_det n t

theorem paper_full_determinant (n : ℕ) (t : ℝ) :
    (sharpFamily n t).det = epsilon n t^(n*(n-1)/2) := by
  exact sharpFamily_det n t

theorem paper_spectral_minor_ratio {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    Tendsto (fun t : ℝ => ((sharpFamily n t).submatrix rows cols).det /
      (epsilon n t^(s*(s-1)/2) * (prefixMatrix hs.le rows t).det * (prefixMatrix hs.le cols t).det))
      (𝓝[>] 0) (𝓝 1) := by
  exact spectral_minor_ratio hs rows cols

theorem paper_all_minors_nonzero (n : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ s : Fin (n+1), ∀ rows cols : Fin s.val ↪ Fin n,
      ((sharpFamily n t).submatrix rows cols).det ≠ 0 := by
  exact all_minors_eventually_nonzero n

end NLA.RA02.Paper

