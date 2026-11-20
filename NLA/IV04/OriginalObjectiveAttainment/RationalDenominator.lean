module

/- Actual reduced denominator bounds from an actual integer fraction. -/
public import NLA.IV04.OriginalObjectiveAttainment.TightIntegerCertificate
public import Mathlib.Data.Rat.Lemmas

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment

theorem divInt_den_le_natAbs (p d : ℤ) (hd : d ≠ 0) : (Rat.divInt p d).den ≤ d.natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hd)
  have h := Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd p d)
  simpa using h

theorem rational_den_le_of_integer_fraction (q : ℚ) (p d : ℤ) (Q : ℕ)
    (hd : d ≠ 0) (hq : q=(p : ℚ)/(d : ℚ)) (hQ : |d| ≤ (Q : ℤ)) : q.den ≤ Q := by
  have hn : d.natAbs ≤ Q := by
    have hc : (d.natAbs : ℤ) ≤ (Q : ℤ) := by simpa only [Int.natCast_natAbs] using hQ
    exact_mod_cast hc
  rw [hq,← Rat.divInt_eq_div]
  exact (divInt_den_le_natAbs p d hd).trans hn

theorem divInt_num_natAbs_le_natAbs (p d : ℤ) (hd : d ≠ 0) :
    (Rat.divInt p d).num.natAbs ≤ p.natAbs := by
  by_cases hp : p=0
  · simp [hp]
  · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hp)
      (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd p hd))

theorem rational_num_natAbs_le_of_integer_fraction (q : ℚ) (p d : ℤ) (Q : ℕ)
    (hd : d ≠ 0) (hq : q=(p : ℚ)/(d : ℚ)) (hQ : |p| ≤ (Q : ℤ)) : q.num.natAbs ≤ Q := by
  have hn : p.natAbs ≤ Q := by
    have hc : (p.natAbs : ℤ) ≤ (Q : ℤ) := by simpa only [Int.natCast_natAbs] using hQ
    exact_mod_cast hc
  rw [hq,← Rat.divInt_eq_div]
  exact (divInt_num_natAbs_le_natAbs p d hd).trans hn

#print axioms divInt_den_le_natAbs
#print axioms rational_den_le_of_integer_fraction
#print axioms divInt_num_natAbs_le_natAbs
#print axioms rational_num_natAbs_le_of_integer_fraction
end Reference.IV04OriginalObjectiveAttainment
