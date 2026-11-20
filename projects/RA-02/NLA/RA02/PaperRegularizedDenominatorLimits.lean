module

public import NLA.RA02.PaperHermitianTailDefinitions
public import NLA.RA02.PaperBestShift

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem regularizedCorrelation_tail_limit {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) (r : ℕ) (hr : r ≤ n) :
    Tendsto (fun δ => hermitianRankTail (regularizedCorrelation C δ) r)
      (𝓝[>] 0) (𝓝 (NLA.RA02.rankTail C hC.isHermitian r)) := by
  have hs : ContinuousAt (fun δ : ℝ => (1+δ)⁻¹) 0 :=
    (continuousAt_const.add continuousAt_id).inv₀ (by norm_num)
  have ht : Tendsto (fun δ : ℝ => (1+δ)⁻¹ *
      (NLA.RA02.rankTail C hC.isHermitian r + δ*(n-r : ℕ)))
      (𝓝[>] 0) (𝓝 (NLA.RA02.rankTail C hC.isHermitian r)) := by
    have hc : ContinuousAt (fun δ : ℝ => (1+δ)⁻¹ *
        (NLA.RA02.rankTail C hC.isHermitian r + δ*(n-r : ℕ))) 0 :=
      hs.mul (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hd : 0 < δ := hδ
  simp only [hermitianRankTail,dif_pos (regularizedCorrelation_posDef C hC hd).isHermitian]
  exact (regularizedCorrelation_rankTail C hC r hr δ hd).symm

theorem regularizedCorrelation_best_error_bounds {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) (r : ℕ) (hr : r ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    (1+δ)⁻¹^2*rectangularBestRankErrorSquared C r ≤
      rectangularBestRankErrorSquared (regularizedCorrelation C δ) r ∧
    rectangularBestRankErrorSquared (regularizedCorrelation C δ) r ≤
      (1+δ)⁻¹^2*(rectangularBestRankErrorSquared C r +
        2*δ*NLA.RA02.realTrace C + δ^2*(n-r : ℕ)) := by
  have hb := best_error_identity_shift_bounds C hC r hr δ hδ.le
  rw [regularizedCorrelation,rectangularBest_real_smul]
  exact ⟨mul_le_mul_of_nonneg_left hb.1 (sq_nonneg _),
    mul_le_mul_of_nonneg_left hb.2 (sq_nonneg _)⟩

theorem regularizedCorrelation_best_error_limit {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) (r : ℕ) (hr : r ≤ n) :
    Tendsto (fun δ => rectangularBestRankErrorSquared (regularizedCorrelation C δ) r)
      (𝓝[>] 0) (𝓝 (rectangularBestRankErrorSquared C r)) := by
  have hs : ContinuousAt (fun δ : ℝ => (1+δ)⁻¹^2) 0 :=
    ((continuousAt_const.add continuousAt_id).inv₀ (by norm_num)).pow 2
  have hl : Tendsto (fun δ : ℝ => (1+δ)⁻¹^2*rectangularBestRankErrorSquared C r)
      (𝓝[>] 0) (𝓝 (rectangularBestRankErrorSquared C r)) := by
    have hc : ContinuousAt (fun δ : ℝ => (1+δ)⁻¹^2*rectangularBestRankErrorSquared C r) 0 :=
      hs.mul continuousAt_const
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun δ : ℝ => (1+δ)⁻¹^2*(rectangularBestRankErrorSquared C r +
      2*δ*NLA.RA02.realTrace C + δ^2*(n-r : ℕ)))
      (𝓝[>] 0) (𝓝 (rectangularBestRankErrorSquared C r)) := by
    have hp : ContinuousAt (fun δ : ℝ => rectangularBestRankErrorSquared C r +
        2*δ*NLA.RA02.realTrace C + δ^2*(n-r : ℕ)) 0 := by fun_prop
    have hc : ContinuousAt (fun δ : ℝ => (1+δ)⁻¹^2*(rectangularBestRankErrorSquared C r +
        2*δ*NLA.RA02.realTrace C + δ^2*(n-r : ℕ))) 0 := hs.mul hp
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (regularizedCorrelation_best_error_bounds C hC r hr δ hδ).1
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (regularizedCorrelation_best_error_bounds C hC r hr δ hδ).2

#print axioms regularizedCorrelation_best_error_limit
end NLA.RA02.Paper
