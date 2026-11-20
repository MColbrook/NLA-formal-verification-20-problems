module

public import NLA.RA02.PaperInterpolationEquations
public import NLA.RA02.PaperSharpFamily

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem continuousAt_mulVec {m n : ℕ} {A : ℝ → Matrix (Fin m) (Fin n) ℝ}
    {v : ℝ → Fin n → ℝ} {t : ℝ} (hA : ContinuousAt A t) (hv : ContinuousAt v t) :
    ContinuousAt (fun u => A u *ᵥ v u) t :=
  (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp (hA.prodMk hv)

def missingCoefficientsExtension {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Fin s → ℝ := t • (scaledPrefixInverse hs.le rows t *ᵥ missingNextColumnVector rows)

theorem continuousAt_missingCoefficientsExtension {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    ContinuousAt (missingCoefficientsExtension hs rows) 0 :=
  continuousAt_id.smul (continuousAt_mulVec (continuousAt_scaledPrefixInverse hs.le rows) continuousAt_const)

def missingResidualExtension {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Fin n → ℝ := nextColumn hs t -
      ((lower n t).submatrix id (Fin.castLE hs.le)) *ᵥ missingCoefficientsExtension hs rows t

theorem continuousAt_missingResidualExtension {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    ContinuousAt (missingResidualExtension hs rows) 0 := by
  have hn : Continuous (nextColumn hs) :=
    continuous_pi (fun i => (continuous_lower n).matrix_elem i ⟨s,hs⟩)
  have hM : Continuous (fun t => (lower n t).submatrix id (Fin.castLE hs.le)) :=
    continuous_matrix (fun i j => (continuous_lower n).matrix_elem i (Fin.castLE hs.le j))
  exact hn.continuousAt.sub (continuousAt_mulVec hM.continuousAt
    (continuousAt_missingCoefficientsExtension hs rows))

theorem missingResidualExtension_zero {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    missingResidualExtension hs rows 0 = Pi.single ⟨s,hs⟩ 1 := by
  ext i
  simp [missingResidualExtension, missingCoefficientsExtension, nextColumn, lower_zero,
    Matrix.one_apply, Pi.single_apply, eq_comm]

theorem interpolation_missing_norm_limit {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (hm : (⟨s,hs⟩ : Fin n) ∉ Set.range rows) :
    Tendsto (interpolationSquaredNorm hs rows) (𝓝[>] 0) (𝓝 1) := by
  let f : (Fin n → ℝ) → ℝ := fun w => ∑ i, (w i)^2
  have hf : Continuous f := continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)
  have he := hf.continuousAt.comp (continuousAt_missingResidualExtension hs rows)
  have hzero : f (missingResidualExtension hs rows 0) = 1 := by
    rw [missingResidualExtension_zero]
    simp [f, Pi.single_apply]
  have ht : Tendsto (fun t => f (missingResidualExtension hs rows t)) (𝓝[>] 0) (𝓝 1) := by
    change Tendsto (f ∘ missingResidualExtension hs rows) _ _
    rw [← hzero]
    exact he.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  unfold interpolationSquaredNorm interpolationResidual
  rw [missing_next_coefficients hs rows hm (ne_of_gt (show 0 < t from ht))]
  rfl

theorem interpolation_missing_reciprocal_limit {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (hm : (⟨s,hs⟩ : Fin n) ∉ Set.range rows) :
    Tendsto (fun t => (interpolationSquaredNorm hs rows t)⁻¹) (𝓝[>] 0) (𝓝 1) := by
  simpa only [inv_one] using (interpolation_missing_norm_limit hs rows hm).inv₀ one_ne_zero

#print axioms interpolation_missing_reciprocal_limit
end NLA.RA02.Paper
