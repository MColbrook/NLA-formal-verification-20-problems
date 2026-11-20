module

public import NLA.MD06.PairingTraceNonnegative.Nonnegative
public import NLA.MD06.SpectralTraceBound.GapTraceBound
public import NLA.MD06.SpectralTraceBound.GapRootBounds
public import NLA.MD06.NonbacktrackingWalkExposure.MeanDefinitions
public import NLA.MD06.CubicConfiguration.CanonicalPairing

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06CenteredMarkov
open Reference.RootMD06SpectralTrace Reference.RootMD06PairingTrace
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open Reference.MD06Nonbacktracking Reference.MD06Spectral Reference.MD06WalkExposure
open scoped BigOperators

theorem actual_pairing_finite_markov {n : ℕ} (E : Pairing n → Prop)
    (f : Pairing n → ℝ) (c : ℝ) (hf : ∀ p, 0 ≤ f p)
    (hE : ∀ p, E p → c ≤ f p) :
    c * PairingProbability n E ≤ PairingMean n f := by
  classical
  let s := Finset.univ.filter E
  have hsum : c * (Fintype.card {p : Pairing n // E p} : ℝ) ≤
      ∑ p : Pairing n, f p := by
    calc
      c * (Fintype.card {p : Pairing n // E p} : ℝ) = ∑ _p ∈ s, c := by
        simp [s, Fintype.card_subtype, mul_comm]
      _ ≤ ∑ p ∈ s, f p := Finset.sum_le_sum (by
        intro p hp
        exact hE p (Finset.mem_filter.mp hp).2)
      _ ≤ ∑ p : Pairing n, f p := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (by intro p _ _; exact hf p)
  unfold PairingProbability PairingMean
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

theorem actual_centered_trace_pairing_mean (k m : ℕ) :
    PairingMean (Size k) (fun p =>
      Matrix.trace (NonbacktrackingMatrix p ^ (2 * m)) - (2 : ℝ) ^ (2 * m) +
        2 * Size k * (2 : ℝ) ^ m) =
      MeanNonbacktrackingTrace (Size k) (2 * m) - (2 : ℝ) ^ (2 * m) +
        2 * Size k * (2 : ℝ) ^ m := by
  classical
  have hc : (Fintype.card (Pairing (Size k)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Pairing (Size k))))
  simp only [MeanNonbacktrackingTrace, PairingMean, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hc]

theorem actual_small_sorted_gap_pairing_probability_bound (k m : ℕ)
    (hn : 2 ≤ Size k) :
    GapRoot ^ (2 * m) * PairingProbability (Size k) (fun p =>
      ∃ h : IsSimplePairing p, LaplacianGap (configurationGraph ⟨p, h⟩) hn < 1 / 10) ≤
      MeanNonbacktrackingTrace (Size k) (2 * m) - (2 : ℝ) ^ (2 * m) +
        2 * Size k * (2 : ℝ) ^ m := by
  have hb := actual_pairing_finite_markov
    (fun p : Pairing (Size k) => ∃ h : IsSimplePairing p,
      LaplacianGap (configurationGraph ⟨p, h⟩) hn < 1 / 10)
    (fun p => Matrix.trace (NonbacktrackingMatrix p ^ (2 * m)) - (2 : ℝ) ^ (2 * m) +
      2 * Size k * (2 : ℝ) ^ m) (GapRoot ^ (2 * m))
    (fun p => actual_all_pairings_centered_even_trace_nonnegative p (by omega) m)
    (by
      intro p hp
      obtain ⟨h, hgap⟩ := hp
      have hs := actual_small_sorted_gap_nonbacktracking_trace_lower_bound ⟨p, h⟩ hn hgap m
      linarith)
  rwa [actual_centered_trace_pairing_mean] at hb

theorem actual_conditioned_small_sorted_gap_probability_bound (k m : ℕ)
    (hn : 2 ≤ Size k) (hs : 0 < PairingProbability (Size k) IsSimplePairing) :
    ConditionedGraphProbability (Size k) (fun G => LaplacianGap G hn < 1 / 10) ≤
      (MeanNonbacktrackingTrace (Size k) (2 * m) - (2 : ℝ) ^ (2 * m) +
        2 * Size k * (2 : ℝ) ^ m) /
      (PairingProbability (Size k) IsSimplePairing * GapRoot ^ (2 * m)) := by
  have hc : 0 < GapRoot ^ (2 * m) := by
    apply pow_pos
    linarith [actual_gap_root_rational_bounds.1]
  have hb := actual_small_sorted_gap_pairing_probability_bound k m hn
  have hm : PairingProbability (Size k) (fun p =>
      ∃ h : IsSimplePairing p, LaplacianGap (configurationGraph ⟨p, h⟩) hn < 1 / 10) ≤
      (MeanNonbacktrackingTrace (Size k) (2 * m) - (2 : ℝ) ^ (2 * m) +
        2 * Size k * (2 : ℝ) ^ m) / GapRoot ^ (2 * m) := by
    apply (le_div_iff₀ hc).2
    nlinarith
  unfold ConditionedGraphProbability
  calc
    _ ≤ ((MeanNonbacktrackingTrace (Size k) (2 * m) - (2 : ℝ) ^ (2 * m) +
        2 * Size k * (2 : ℝ) ^ m) / GapRoot ^ (2 * m)) /
        PairingProbability (Size k) IsSimplePairing := div_le_div_of_nonneg_right hm hs.le
    _ = _ := by rw [div_div]; congr 1; ring

#print axioms actual_pairing_finite_markov
#print axioms actual_centered_trace_pairing_mean
#print axioms actual_small_sorted_gap_pairing_probability_bound
#print axioms actual_conditioned_small_sorted_gap_probability_bound
end Reference.RootMD06CenteredMarkov
