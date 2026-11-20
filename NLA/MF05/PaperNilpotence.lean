module

public import NLA.MF05.PaperHolder
public import NLA.MF07.Interspersed

@[expose] public section

/- The zero-radius clause of the paper's growth theorem, for compact families. -/
set_option autoImplicit false
open NLA.MF07
noncomputable section
namespace NLA.MF05.Paper

theorem complex_zero_radius_growth_at_dimension {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hr : jointSpectralRadius M = 0) :
    familyGrowth M d = 0 := by
  apply le_antisymm _ (familyGrowth_nonneg M hM hne d)
  apply le_of_forall_pos_le_add
  intro ε hε
  let C : ℝ := (d : ℝ) * (2*(d : ℝ)^2*L)^d
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let s : ℝ := 1 + C/ε
  have hs : 1 ≤ s := by
    have hnonneg := div_nonneg hC hε.le
    dsimp [s]
    linarith
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsmall : C/s ≤ ε := by
    apply (div_le_iff₀ hspos).mpr
    have heq : ε*s = ε+C := by dsimp [s]; field_simp
    rw [heq]
    linarith
  have h := general_quantitative_comparison hd M hM hne L s hL hML hs d
  have heq : comparisonFactor d s * (comparisonRate d M L s)^d = C/s := by
    simp only [comparisonFactor, comparisonRate, hr, zero_add]
    dsimp [C]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    simp only [Nat.succ_sub_one, div_pow, pow_succ]
    field_simp
  rw [heq] at h
  simpa using h.trans hsmall

theorem complex_zero_radius_nilpotent {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hr : jointSpectralRadius M = 0)
    (w : List (Square d)) (hw : WordIn M w) (hlen : d ≤ w.length) : matrixProduct w = 0 := by
  have hz := complex_zero_radius_growth_at_dimension hd M hM hne L hL hML hr
  have hu := family_growth_submultiplicative hd M hM hne d (w.length-d)
  rw [Nat.add_sub_of_le hlen, hz, zero_mul] at hu
  have hword := word_le_familyGrowth M hM w.length w rfl hw
  apply (spectralNorm_eq_zero_iff _).mp
  exact le_antisymm (hword.trans hu) (spectralNorm_nonneg _)

theorem real_zero_radius_nilpotent {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : IsCompact M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hr : realRadius M = 0)
    (w : List (RealSquare d)) (hw : ∀ A ∈ w, A ∈ M) (hlen : d ≤ w.length) :
    realMatrixProduct w = 0 := by
  have hwc : WordIn (complexify '' M) (w.map complexify) := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    exact ⟨A, hw A hA, rfl⟩
  have h := complex_zero_radius_nilpotent hd (complexify '' M)
    (hM.image continuous_complexify) (hne.image complexify) L hL
    (complexify_normBall M L hML) (by rwa [complexify_radius]) (w.map complexify)
    hwc (by simpa using hlen)
  rw [complexify_product] at h
  ext i j
  have he := congrArg (fun A : Square d => (A i j).re) h
  simpa [complexify] using he

#print axioms complex_zero_radius_nilpotent
#print axioms real_zero_radius_nilpotent
end NLA.MF05.Paper
