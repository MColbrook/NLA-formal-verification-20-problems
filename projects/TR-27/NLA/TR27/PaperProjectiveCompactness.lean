module

public import NLA.TR27.PaperProjectiveTopology
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

theorem continuous_coordinate_projective_mk (n : ℕ) :
    Continuous (Projectivization.mk' ℂ : {v : Fin n → ℂ // v ≠ 0} → ℙ ℂ (Fin n → ℂ)) :=
  continuous_coinduced_rng

/-- The unit sphere surjects onto the usual projective quotient. This proves
compactness without putting a topology on a curve by transport. -/
theorem coordinateProjective_compact (n : ℕ) : CompactSpace (ℙ ℂ (Fin n → ℂ)) := by
  let S := Metric.sphere (0 : Fin n → ℂ) 1
  have hne (v : S) : (v.val : Fin n → ℂ) ≠ 0 := by
    intro hz
    have h := v.property
    simpa [S, Metric.mem_sphere, hz] using h
  let f : S → ℙ ℂ (Fin n → ℂ) := fun v => Projectivization.mk ℂ v.val (hne v)
  have hf : Continuous f := (continuous_coordinate_projective_mk n).comp
    (continuous_subtype_val.subtype_mk hne)
  have hsurj : Function.Surjective f := by
    intro p
    let c : ℂ := (‖p.rep‖ : ℂ)⁻¹
    have hn : ‖p.rep‖ ≠ 0 := norm_ne_zero_iff.mpr p.rep_nonzero
    have hc : c ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
    have hnorm : ‖c • p.rep‖ = 1 := by
      simp only [c, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      exact inv_mul_cancel₀ hn
    have hm : c • p.rep ∈ S := by
      simpa only [S, Metric.mem_sphere, dist_zero_right] using hnorm
    refine ⟨⟨c • p.rep,hm⟩, ?_⟩
    change Projectivization.mk ℂ (c • p.rep) _ = p
    calc
      _ = Projectivization.mk ℂ p.rep p.rep_nonzero :=
        (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,rfl⟩
      _ = p := p.mk_rep
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Fin n → ℂ) 1)
  constructor
  rw [← Set.range_eq_univ.mpr hsurj]
  exact isCompact_range hf

#print axioms coordinateProjective_compact
end NLA.TR27.Paper
