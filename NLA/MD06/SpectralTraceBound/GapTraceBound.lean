module

public import NLA.MD06.SpectralTraceBound.MatrixSpectral

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06SpectralTrace
open Reference.MD06Nonbacktracking Reference.MD06CubicConfiguration
open Reference.MD06Spectral
open scoped BigOperators

theorem actual_small_sorted_gap_trace_lower_bound {n : ℕ}
    (p : SimpleConfiguration n) (hn : 2 ≤ n)
    (hgap : LaplacianGap (configurationGraph p) hn < 1 / 10) (m : ℕ) :
    (2 : ℝ) ^ (2 * m) + GapRoot ^ (2 * m) - 2 * n * (2 : ℝ) ^ m ≤
      Matrix.trace (TracePolynomial (AdjacencyMatrix p.val) (2 * m)) := by
  classical
  let b : Fin n := ⟨n - 1, by omega⟩
  let g : Fin n := ⟨n - 2, by omega⟩
  have hbg : b ≠ g := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [b, g] at hv
    omega
  let f : Fin n → ℝ := fun i =>
    ScalarTracePolynomial (3 - LaplacianEigenvalues (configurationGraph p) i) (2 * m) +
      2 * (2 : ℝ) ^ m
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    dsimp [f]
    linarith [actual_scalar_even_uniform_lower_bound
      (3 - LaplacianEigenvalues (configurationGraph p) i) m]
  have hsum : f b + f g ≤ ∑ i : Fin n, f i := by
    calc
      f b + f g = ∑ i ∈ ({b, g} : Finset (Fin n)), f i := by simp [hbg]
      _ ≤ ∑ i : Fin n, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by
          intro i _ _
          exact hf i)
  have hb : ScalarTracePolynomial
      (3 - LaplacianEigenvalues (configurationGraph p) b) (2 * m) =
      (2 : ℝ) ^ (2 * m) + 1 := by
    rw [actual_laplacian_bottom_eigenvalue_zero (configurationGraph p) (by omega), sub_zero,
      actual_scalar_three_value]
  have hg : GapRoot ^ (2 * m) ≤ ScalarTracePolynomial
      (3 - LaplacianEigenvalues (configurationGraph p) g) (2 * m) := by
    apply actual_scalar_gap_power_lower_bound
    change 29 / 10 ≤ 3 - LaplacianGap (configurationGraph p) hn
    linarith
  have hpow : 0 ≤ (2 : ℝ) ^ m := by positivity
  dsimp [f] at hsum
  rw [hb] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [actual_matrix_trace_polynomial_spectral_sum]
  nlinarith

theorem actual_small_sorted_gap_nonbacktracking_trace_lower_bound {n : ℕ}
    (p : SimpleConfiguration n) (hn : 2 ≤ n)
    (hgap : LaplacianGap (configurationGraph p) hn < 1 / 10) (m : ℕ) :
    GapRoot ^ (2 * m) - 2 * n * (2 : ℝ) ^ m ≤
      Matrix.trace (NonbacktrackingMatrix p.val ^ (2 * m)) - (2 : ℝ) ^ (2 * m) := by
  have hs := actual_small_sorted_gap_trace_lower_bound p hn hgap m
  have ht := (actual_nonbacktracking_trace_bounds p.val (2 * m)).1
  linarith

#print axioms actual_small_sorted_gap_trace_lower_bound
#print axioms actual_small_sorted_gap_nonbacktracking_trace_lower_bound

end Reference.RootMD06SpectralTrace
