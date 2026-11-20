module

public import NLA.RA02.PaperPrefixConclusions
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Topology
open Filter Asymptotics
namespace NLA.RA02.Paper

theorem paper_lower_entries (n : ℕ) (t : ℝ) (i j : Fin n) :
    lower n t i j = if i = j then 1 else
      if j < i then t^(j.val+1)/(i.val+j.val+2 : ℕ) else 0 := by
  rfl

theorem paper_prefix_semantics {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    prefixMatrix hs rows t = (lower n t).submatrix rows (Fin.castLE hs) ∧
    prefixDegree hs rows = ∑ j : Fin s,
      if Fin.castLE hs j ∈ Set.range rows then 0 else j.val+1 := by
  exact ⟨rfl, rfl⟩

theorem paper_prefix_asymptotic {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∃ e : ℝ → ℝ,
      e =O[𝓝[>] 0] (fun t : ℝ => t) ∧
      ∀ t : ℝ, (prefixMatrix hs rows t).det = κ * t^(prefixDegree hs rows) * (1+e t) := by
  exact prefix_asymptotic hs rows

theorem paper_prefix_invertible {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, IsUnit (prefixMatrix hs rows t) := by
  filter_upwards [prefix_eventually_nonsingular hs rows] with t ht
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht)

theorem paper_prefix_inverse_norm {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    (fun t : ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) (prefixMatrix hs rows t)⁻¹)
      =O[𝓝[>] 0] (fun t : ℝ => (t^s)⁻¹) := by
  exact prefix_inverse_bigO hs rows

end NLA.RA02.Paper
