module

public import NLA.RA02.PaperPrefixInverse

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Topology
open Filter Asymptotics
namespace NLA.RA02.Paper

theorem prefix_asymptotic {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∃ e : ℝ → ℝ,
      e =O[𝓝[>] 0] (fun t : ℝ => t) ∧
      ∀ t : ℝ, (prefixMatrix hs rows t).det = κ * t^(prefixDegree hs rows) * (1+e t) := by
  let κ := (normalizedPrefix hs rows 0).det
  have hk : κ ≠ 0 := normalizedPrefix_zero_det_ne_zero hs rows
  refine ⟨κ, hk, (fun t => κ⁻¹ * ((normalizedPrefix hs rows t).det-κ)), ?_, ?_⟩
  · exact (normalized_det_error hs rows).const_mul_left κ⁻¹
  · intro t
    rw [prefix_det_factorization]
    field_simp
    <;> ring

theorem prefix_inverse_bigO {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    (fun t : ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) (prefixMatrix hs rows t)⁻¹)
      =O[𝓝[>] 0] (fun t : ℝ => (t^s)⁻¹) := by
  obtain ⟨C, _, he⟩ := prefix_inverse_bound hs rows
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [he, self_mem_nhdsWithin] with t hb ht
  have hp : (0 : ℝ) < t^s := pow_pos (show 0 < t from ht) s
  simpa only [Real.norm_eq_abs, abs_inv, abs_of_pos hp, div_eq_mul_inv] using hb

#print axioms prefix_asymptotic
end NLA.RA02.Paper
