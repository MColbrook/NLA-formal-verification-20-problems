module

/- Reference-only arithmetic facts for exact rational endpoint recovery.
   No polyhedron, certificate, oracle correctness, or runtime contract is assumed. -/
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04ExactOutputSupport

 theorem rational_separation {q r : ℚ} {Q : ℕ} (hQ : 0 < Q)
    (hq : q.den ≤ Q) (hr : r.den ≤ Q) (hne : q ≠ r) :
    1 / (Q : ℚ)^2 ≤ |q-r| := by
  have hd : 0 < ((q-r).den : ℚ) := by exact_mod_cast (q-r).pos
  have hn : (1 : ℚ) ≤ |((q-r).num : ℚ)| := by
    exact_mod_cast Int.one_le_abs (Rat.num_ne_zero.mpr (sub_ne_zero.mpr hne))
  have hb : (q-r).den ≤ Q^2 := by
    have h := Nat.le_of_dvd (Nat.mul_pos q.pos r.pos) (Rat.sub_den_dvd q r)
    have hm : q.den*r.den ≤ Q*Q := Nat.mul_le_mul hq hr
    simpa only [pow_two] using h.trans hm
  calc
    1 / (Q : ℚ)^2 ≤ 1 / ((q-r).den : ℚ) := by
      apply (div_le_div_iff₀ (by positivity) hd).2
      simpa only [one_mul] using
        (show ((q-r).den : ℚ) ≤ (Q : ℚ)^2 by exact_mod_cast hb)
    _ ≤ |q-r| := by
      conv_rhs => rw [← Rat.num_div_den (q-r), abs_div, abs_of_pos hd]
      exact div_le_div_of_nonneg_right hn hd.le

 theorem unique_rational_in_narrow_bracket {q r L U : ℚ} {Q : ℕ}
    (hQ : 0 < Q) (hq : q.den ≤ Q) (hr : r.den ≤ Q)
    (hLq : L ≤ q) (hqU : q ≤ U) (hLr : L ≤ r) (hrU : r ≤ U)
    (hwidth : U-L < 1/(Q : ℚ)^2) : q=r := by
  by_contra hne
  have hsep := rational_separation hQ hq hr hne
  have hab : |q-r| ≤ U-L := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

 theorem near_optimum_candidate_exact {q maximum L : ℚ} {Q : ℕ}
    (hQ : 0 < Q) (hq : q.den ≤ Q) (hmax : maximum.den ≤ Q)
    (hqmax : q ≤ maximum) (hLq : L < q)
    (hgap : maximum-L < 1/(Q : ℚ)^2) : q=maximum := by
  by_contra hne
  have hsep := rational_separation hQ hq hmax hne
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hqmax)] at hsep
  linarith

 theorem midpoint_error_bound {q : ℚ} {L U : ℝ}
    (hLq : L ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ U) :
    |(L+U)/2-(q : ℝ)| ≤ (U-L)/2 := by
  exact abs_le.mpr ⟨by linarith, by linarith⟩

 theorem midpoint_is_continued_fraction_convergent {q : ℚ} {L U : ℝ} {Q : ℕ}
    (hQ : 0 < Q) (hq : q.den ≤ Q)
    (hLq : L ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ U)
    (hwidth : U-L < 1/(2*(Q : ℝ)^2)) :
    ∃ k : ℕ, (GenContFract.of ((L+U)/2)).convs k = (q : ℝ) := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : (q.den : ℝ) ≤ Q := by exact_mod_cast hq
  have hsq : (q.den : ℝ)^2 ≤ (Q : ℝ)^2 := by nlinarith
  have hinv : 1/(2*(Q : ℝ)^2) ≤ 1/(2*(q.den : ℝ)^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  apply Real.exists_convs_eq_rat
  have hmid := midpoint_error_bound hLq hqU
  have hw : 0 ≤ U-L := by linarith
  have hnear : |(L+U)/2-(q : ℝ)| < 1/(2*(Q : ℝ)^2) := by linarith
  exact hnear.trans_le hinv

#print axioms rational_separation
#print axioms unique_rational_in_narrow_bracket
#print axioms near_optimum_candidate_exact
#print axioms midpoint_error_bound
#print axioms midpoint_is_continued_fraction_convergent
end Reference.IV04ExactOutputSupport
