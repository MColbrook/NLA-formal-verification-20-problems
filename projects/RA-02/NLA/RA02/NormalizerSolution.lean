module

public import NLA.RA02.PaperNormalizers
public import NLA.RA02.PaperResidualNorms
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem paper_residual_semantics {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin s ↪ Fin n) :
    interpolatoryResidual A rows cols =
      A - A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id := by
  rfl

theorem paper_trace_semantics {n s : ℕ} (rows : Fin s ↪ Fin n) (t : ℝ) :
    paperTrace rows t = (interpolatoryResidual (sharpFamily n t) rows rows).trace := by
  rfl

theorem paper_frobenius_semantics {n s : ℕ} (rows cols : Fin s ↪ Fin n) (t : ℝ) :
    paperFrobeniusSquared rows cols t =
      ‖(WithLp.toLp 2 (fun p : Fin n × Fin n => interpolatoryResidual (sharpFamily n t) rows cols p.1 p.2) :
        EuclideanSpace ℝ (Fin n × Fin n))‖^2 := by
  exact residual_frobenius_squared_norm rows cols t

theorem paper_trace_asymptotic {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    Tendsto (fun t => paperTrace rows t / (epsilon n t^s * interpolationSquaredNorm hs rows t))
      (𝓝[>] 0) (𝓝 1) := by
  exact trace_asymptotic_ratio hs rows

theorem paper_frobenius_asymptotic {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    Tendsto (fun t => paperFrobeniusSquared rows cols t /
      (epsilon n t^(2*s) * interpolationSquaredNorm hs rows t * interpolationSquaredNorm hs cols t))
      (𝓝[>] 0) (𝓝 1) := by
  exact frobenius_asymptotic_ratio hs rows cols

theorem paper_trace_indicator {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    Tendsto (fun t => epsilon n t^s / paperTrace rows t) (𝓝[>] 0)
      (𝓝 (if (⟨s,hs⟩ : Fin n) ∉ Set.range rows then 1 else 0)) := by
  exact trace_indicator_limit hs rows

theorem paper_frobenius_indicator {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    Tendsto (fun t => epsilon n t^(2*s) / paperFrobeniusSquared rows cols t) (𝓝[>] 0)
      (𝓝 ((if (⟨s,hs⟩ : Fin n) ∉ Set.range rows then 1 else 0) *
        (if (⟨s,hs⟩ : Fin n) ∉ Set.range cols then 1 else 0))) := by
  exact frobenius_indicator_limit hs rows cols

end NLA.RA02.Paper

