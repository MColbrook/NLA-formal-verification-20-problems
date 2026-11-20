module

public import NLA.MF05.RadiusTransfer

@[expose] public section

/- The coefficient-one improvement printed for dimension one. -/
set_option autoImplicit false
noncomputable section
namespace NLA.MF05
open NLA.MF07

theorem scalar_radius_transfer (M N : Set (Square 1))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) :
    jointSpectralRadius N ≤ jointSpectralRadius M + spectralHausdorff M N := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let s : ℝ := 1 + 2*L/ε
  have hs : 1 ≤ s := by
    have hnonneg : 0 ≤ 2*L/ε := by positivity
    dsimp [s]
    linarith
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsmall : 2*L/s ≤ ε := by
    apply (div_le_iff₀ hspos).mpr
    have heq : ε*s = ε + 2*L := by dsimp [s]; field_simp
    rw [heq]
    linarith
  have h := hausdorff_radius_transfer (d:=1) (by decide) M N hM hneM hN hneN L s hL hML hs
  norm_num [comparisonRate, comparisonFactor] at h
  linarith

theorem scalar_holder_coefficient_one (M N : Set (Square 1))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hNL : InNormBall N L) :
    |jointSpectralRadius M - jointSpectralRadius N| ≤ spectralHausdorff M N := by
  have hn := scalar_radius_transfer M N hM hneM hN hneN L hL hML
  have hm := scalar_radius_transfer N M hN hneN hM hneM L hL hNL
  have he : spectralHausdorff N M = spectralHausdorff M N := Metric.hausdorffDist_comm
  rw [he] at hm
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

#print axioms scalar_holder_coefficient_one
end NLA.MF05
