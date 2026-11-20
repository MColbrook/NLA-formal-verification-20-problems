module

public import NLA.MF12.PaperRationalRealization

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

theorem real_dimension_realization (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ d : ℕ, d = paperDimension γ ∧ 1 ≤ d ∧
      ∃ A P : Square d, Realizes A P γ := by
  let m : ℕ := ⌊γ⌋₊
  have hm : (m : ℝ) ≤ γ := Nat.floor_le hγ
  by_cases hγm : γ = (m : ℝ)
  · refine ⟨m+1, ?_, by omega, jordanMatrix m, 0, ?_⟩
    · change m+1 = if γ = (m : ℝ) then m+1 else 6*(m+1)
      rw [if_pos hγm]
    · rw [hγm]
      exact integer_realization m
  · let α : ℝ := γ - (m : ℝ)
    have hα : 0 < α := sub_pos.mpr (lt_of_le_of_ne hm (Ne.symm hγm))
    have hα1 : α < 1 := by
      have hlt : γ < (m : ℝ) + 1 := Nat.lt_floor_add_one γ
      dsimp only [α]
      linarith
    have he : α + (m : ℝ) = γ := by dsimp only [α]; ring
    have ht := fractional_tensor_growth α hα hα1 m
    have hb := ht.2.2.2
    have hr := roots_of_polynomial_growth _ _ _ _
      (show 0 ≤ α + (m : ℝ) by positivity) ht.2.1
      (ht.2.1.trans_le ht.2.2.1) hb
    refine ⟨6*(m+1), ?_, by omega, liftedA α m, liftedP m, ?_⟩
    · change 6*(m+1) = if γ = (m : ℝ) then m+1 else 6*(m+1)
      rw [if_neg hγm]
    · simpa only [he] using
        (show Realizes (liftedA α m) (liftedP m) (α + (m : ℝ)) from
          ⟨ht.1, liftedLower α m, liftedUpper α m, ht.2.1, ht.2.2.1, hb, hr⟩)

theorem dimension_integer (m : ℕ) : paperDimension (m : ℝ) = m+1 := by
  simp [paperDimension]

theorem dimension_fractional (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) :
    paperDimension γ = 6 := by
  have hf : ⌊γ⌋₊ = 0 := Nat.floor_eq_zero.mpr hγ1
  simp [paperDimension, hf, hγ.ne']

theorem dimension_noninteger (γ : ℝ) (hγ : ¬ ∃ m : ℕ, γ = (m : ℝ)) :
    paperDimension γ = 6*(⌊γ⌋₊+1) := by
  exact if_neg (fun h => hγ ⟨_, h⟩)

/-- The same pair can satisfy both the dimension bound and, when applicable,
    the rational-entry conclusion. -/
theorem full_main_realization (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ d : ℕ, d = paperDimension γ ∧ 1 ≤ d ∧
      ∃ A P : Square d, Realizes A P γ ∧
        ((∃ q : ℚ, (q : ℝ) = γ) → ∀ i j, IsDyadic (A i j) ∧ IsDyadic (P i j)) := by
  by_cases hrat : ∃ q : ℚ, (q : ℝ) = γ
  · obtain ⟨q, rfl⟩ := hrat
    have hq : 0 ≤ q := Rat.cast_nonneg.mp hγ
    obtain ⟨d, hd, hdpos, A, P, hAP, hdy⟩ := rational_dyadic_realization q hq
    exact ⟨d, hd, hdpos, A, P, hAP, fun _ => hdy⟩
  · obtain ⟨d, hd, hdpos, A, P, hAP⟩ := real_dimension_realization γ hγ
    exact ⟨d, hd, hdpos, A, P, hAP, fun h => (hrat h).elim⟩

#print axioms full_main_realization
end NLA.MF12.Paper
