module

public import NLA.RA08.OrderedSingular.Definitions
public import NLA.RA08.PaperNuclearTriangularSpectrum
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper.OrderedSingular

theorem actual_gram_posSemidef (m : ℕ) :
    (nuclearTriangularGram m).PosSemidef := by
  exact nuclearGram_posSemidef (nuclearTriangular m)

theorem orderedGram_eq_reindexed {m : ℕ}
    (hG : (nuclearTriangularGram m).IsHermitian) (j : Fin m) :
    orderedGram hG j = hG.eigenvalues (indexReindex m j) := by
  simp [orderedGram, Matrix.IsHermitian.eigenvalues, indexReindex]

theorem orderedGram_antitone {m : ℕ}
    (hG : (nuclearTriangularGram m).IsHermitian) : Antitone (orderedGram hG) := by
  intro i j hij
  exact hG.eigenvalues₀_antitone
    ((Fin.castOrderIso (Fintype.card_fin m).symm).monotone hij)

theorem angle_strictMono (m : ℕ) : StrictMono (nuclearSineAngle (m := m)) := by
  intro i j hij
  unfold nuclearSineAngle
  have hc : ((2*i.val+1 : ℕ) : ℝ) < ((2*j.val+1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2*i.val+1 < 2*j.val+1 by omega)
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hc Real.pi_pos) (by positivity)

theorem actual_difference_eigenvalue_strictMono (m : ℕ) :
    StrictMono (nuclearDifferenceEigenvalue (m := m)) := by
  intro i j hij
  rw [nuclearDifferenceEigenvalue_eq, nuclearDifferenceEigenvalue_eq]
  have hcos := Real.strictAntiOn_cos
    ⟨(nuclearSineAngle_pos i).le, (nuclearSineAngle_lt_pi i).le⟩
    ⟨(nuclearSineAngle_pos j).le, (nuclearSineAngle_lt_pi j).le⟩
    (angle_strictMono m hij)
  linarith

theorem actual_ordered_gram {m : ℕ}
    (hG : (nuclearTriangularGram m).IsHermitian) (j : Fin m) :
    orderedGram hG j = (nuclearDifferenceEigenvalue j)⁻¹ := by
  classical
  obtain ⟨e, he⟩ := nuclearTriangular_spectrum_permutation m
  let q : Fin m ≃ Fin m := e.trans (indexReindex m).symm
  have hq (i : Fin m) : orderedGram hG (q i) = (nuclearDifferenceEigenvalue i)⁻¹ := by
    rw [orderedGram_eq_reindexed]
    have hidx : indexReindex m (q i) = e i := by simp [q]
    rw [hidx]
    exact he i
  have hinv : StrictAnti (fun i : Fin m => (nuclearDifferenceEigenvalue i)⁻¹) := by
    intro i k hik
    exact (inv_lt_inv₀ (nuclearDifferenceEigenvalue_pos k)
      (nuclearDifferenceEigenvalue_pos i)).mpr
      (actual_difference_eigenvalue_strictMono m hik)
  have hmono : StrictMono (q : Fin m → Fin m) := by
    intro i k hik
    by_contra hn
    have hle : q k ≤ q i := le_of_not_gt hn
    have hbound := orderedGram_antitone hG hle
    rw [hq i, hq k] at hbound
    exact (not_le_of_gt (hinv hik)) hbound
  have hid : (q : Fin m → Fin m) = id := hmono.eq_id
  have hj : q j = j := congrFun hid j
  simpa only [hj] using hq j

theorem actual_angle_half {m : ℕ} (j : Fin m) :
    nuclearSineAngle j / 2 =
      ((2*j.val+1 : ℕ) : ℝ) * Real.pi / (4*(m : ℝ)+2) := by
  unfold nuclearSineAngle
  have hd : (2*(m : ℝ)+1) ≠ 0 := by positivity
  have hd' : (4*(m : ℝ)+2) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem actual_ordered_singular {m : ℕ}
    (hG : (nuclearTriangularGram m).IsHermitian) (j : Fin m) :
    orderedSingular hG j =
      1 / (2 * Real.sin (((2*j.val+1 : ℕ) : ℝ) * Real.pi / (4*(m : ℝ)+2))) := by
  rw [orderedSingular, actual_ordered_gram, Real.sqrt_inv]
  have hs : 0 ≤ 2*Real.sin (nuclearSineAngle j/2) := by
    have hp := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [nuclearSineAngle_pos j] : 0 < nuclearSineAngle j/2)
      (by linarith [nuclearSineAngle_lt_pi j, Real.pi_pos] : nuclearSineAngle j/2 < Real.pi)
    positivity
  rw [show nuclearDifferenceEigenvalue j = (2*Real.sin (nuclearSineAngle j/2))^2 by
    unfold nuclearDifferenceEigenvalue; ring, Real.sqrt_sq hs, actual_angle_half, one_div]

#print axioms actual_gram_posSemidef
#print axioms actual_difference_eigenvalue_strictMono
#print axioms actual_ordered_gram
#print axioms actual_angle_half
#print axioms actual_ordered_singular
end NLA.RA08.Paper.OrderedSingular
