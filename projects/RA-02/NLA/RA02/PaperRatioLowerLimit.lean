module

public import NLA.RA02.PaperRegularizedExpectations
public import NLA.RA02.PaperRegularizedDenominatorLimits

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem eventually_ratio_gt_of_lower_limit {ι : Type*} (l : Filter ι)
    (N D : ι → ℝ) (a b : ℝ) (hb : 0 < b) (hN : ∀ i, 0 ≤ N i)
    (hlo : ∀ y < a, ∀ᶠ i in l, y < N i) (hD : Tendsto D l (𝓝 b))
    (q : ℝ) (hq : q < a/b) : ∀ᶠ i in l, q < N i/D i := by
  have hd : ∀ᶠ i in l, 0 < D i := hD.eventually (eventually_gt_nhds hb)
  by_cases hqn : q < 0
  · filter_upwards [hd] with i hi
    exact hqn.trans_le (div_nonneg (hN i) hi.le)
  have hqa : q*b < a := (lt_div_iff₀ hb).mp hq
  obtain ⟨w,hqw,hwa⟩ := exists_between hqa
  have ht : Tendsto (fun i => q*D i) l (𝓝 (q*b)) := tendsto_const_nhds.mul hD
  filter_upwards [hd,ht.eventually (eventually_lt_nhds hqw),hlo w hwa] with i hi hqi hni
  exact (lt_div_iff₀ hi).mpr (hqi.trans hni)

theorem regularizedCorrelation_lu_ratio_lower {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) (r : ℕ) (hr : r ≤ n)
    (hd : 0 < rectangularBestRankErrorSquared C r) (q : ℝ)
    (hq : q < NLA.RA03.expectedError C r/rectangularBestRankErrorSquared C r) :
    ∀ᶠ δ in 𝓝[>] 0, q < NLA.RA03.expectedError (regularizedCorrelation C δ) r /
      rectangularBestRankErrorSquared (regularizedCorrelation C δ) r := by
  exact eventually_ratio_gt_of_lower_limit _ _ _ _ _ hd
    (fun δ => lu_expectedError_nonneg _ r)
    (fun y hy => regularizedCorrelation_lu_lower_limit C r y hy)
    (regularizedCorrelation_best_error_limit C hC r hr) q hq

theorem regularizedCorrelation_cholesky_ratio_lower {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) (r : ℕ) (hr : r ≤ n)
    (hd : 0 < NLA.RA02.rankTail C hC.isHermitian r) (q : ℝ)
    (hq : q < NLA.RA02.expectedTrace C r/NLA.RA02.rankTail C hC.isHermitian r) :
    ∀ᶠ δ in 𝓝[>] 0, q < NLA.RA02.expectedTrace (regularizedCorrelation C δ) r /
      hermitianRankTail (regularizedCorrelation C δ) r := by
  have hlo := regularizedCorrelation_cholesky_lower_limit C hC r
  have hdlim := regularizedCorrelation_tail_limit C hC r hr
  -- The totalized numerator agrees with the actual expectation for positive δ.
  have hN : ∀ δ : ℝ, 0 ≤ (if 0 < δ then NLA.RA02.expectedTrace (regularizedCorrelation C δ) r else 0) := by
    intro δ
    split_ifs with hδ
    · exact NLA.RA02.expectedTrace_nonneg _ (regularizedCorrelation_posDef C hC hδ).posSemidef r
    · exact le_rfl
  have hnlo : ∀ y < NLA.RA02.expectedTrace C r,
      ∀ᶠ δ in 𝓝[>] 0, y < (if 0 < δ then NLA.RA02.expectedTrace (regularizedCorrelation C δ) r else 0) := by
    intro y hy
    filter_upwards [self_mem_nhdsWithin,hlo y hy] with δ hδ hval
    have hp : 0 < δ := hδ
    simpa [hp] using hval
  have hres := eventually_ratio_gt_of_lower_limit (𝓝[>] (0 : ℝ))
    (fun δ => if 0 < δ then NLA.RA02.expectedTrace (regularizedCorrelation C δ) r else 0)
    (fun δ => hermitianRankTail (regularizedCorrelation C δ) r)
    _ _ hd hN hnlo hdlim q hq
  filter_upwards [self_mem_nhdsWithin,hres] with δ hδ hval
  have hp : 0 < δ := hδ
  simpa [hp] using hval

#print axioms regularizedCorrelation_cholesky_ratio_lower
end NLA.RA02.Paper
