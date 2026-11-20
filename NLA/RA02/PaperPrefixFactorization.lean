module

public import NLA.RA02.PaperPrefixLimit
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter Asymptotics
namespace NLA.RA02.Paper

theorem prefix_factorization {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    prefixMatrix hs rows t = normalizedPrefix hs rows t * Matrix.diagonal
      (fun j => if Fin.castLE hs j ∉ Set.range rows then t^(j.val+1) else 1) := by
  ext i j
  rw [Matrix.mul_diagonal]
  change lower n t (rows i) (Fin.castLE hs j) = _
  by_cases hm : Fin.castLE hs j ∉ Set.range rows
  · have he : rows i ≠ Fin.castLE hs j := by
      intro h
      exact hm ⟨i,h⟩
    simp only [normalizedPrefix, if_pos hm, lower, if_neg he]
    by_cases hlt : Fin.castLE hs j < rows i
    · simp only [if_pos hlt, Fin.val_castLE]
      push_cast
      ring
    · simp [hlt]
  · simp only [normalizedPrefix, if_neg hm, mul_one]

theorem prefix_det_factorization {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    (prefixMatrix hs rows t).det = (normalizedPrefix hs rows t).det * t^(prefixDegree hs rows) := by
  rw [prefix_factorization, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  unfold prefixDegree
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : Fin.castLE hs j ∈ Set.range rows <;> simp [hj]

theorem continuous_normalizedPrefix {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    Continuous (normalizedPrefix hs rows) := by
  apply continuous_matrix
  intro i j
  unfold normalizedPrefix lower
  split_ifs <;> fun_prop

theorem differentiable_normalized_det {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    Differentiable ℝ (fun t => (normalizedPrefix hs rows t).det) := by
  simp only [Matrix.det_apply']
  apply Differentiable.fun_sum
  intro σ _
  apply Differentiable.const_mul
  have he : ∀ i : Fin s, Differentiable ℝ (fun t => normalizedPrefix hs rows t (σ i) i) := by
    intro i
    unfold normalizedPrefix lower
    split_ifs <;> (try simp only [div_eq_mul_inv]) <;> fun_prop
  intro t
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (fun i _ => (he i t).hasFDerivAt)).differentiableAt

theorem prefix_leading_ratio {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    Tendsto (fun t : ℝ => (prefixMatrix hs rows t).det / t^(prefixDegree hs rows))
      (𝓝[>] 0) (𝓝 (normalizedPrefix hs rows 0).det) := by
  have ht := ((continuous_normalizedPrefix hs rows).matrix_det).continuousAt.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hz : t ≠ 0 := ne_of_gt ht
  rw [prefix_det_factorization, mul_div_cancel_right₀ _ (pow_ne_zero _ hz)]

theorem prefix_eventually_nonsingular {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (prefixMatrix hs rows t).det ≠ 0 := by
  have he := (prefix_leading_ratio hs rows).eventually
    (eventually_ne_nhds (normalizedPrefix_zero_det_ne_zero hs rows))
  filter_upwards [he] with t ht
  exact (div_ne_zero_iff.mp ht).1

theorem normalized_det_error {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    (fun t : ℝ => (normalizedPrefix hs rows t).det - (normalizedPrefix hs rows 0).det)
      =O[𝓝[>] 0] (fun t : ℝ => t) := by
  have h := ((differentiable_normalized_det hs rows).differentiableAt (x := (0 : ℝ))).isBigO_sub
  simpa only [sub_zero] using h.mono
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)

#print axioms prefix_eventually_nonsingular
end NLA.RA02.Paper
