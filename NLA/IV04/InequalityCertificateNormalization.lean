module

public import NLA.IV04.InequalityIntegerBridge
public import NLA.IV04.AffinePolyhedronSteps.IntegerSignedCertificate
public import NLA.IV04.AffinePolyhedronSteps.GramSize
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
namespace IV04.Paper.InequalityCertificate

 theorem normalize_common_denominator {n : ℕ} (x : Fin n → ℝ)
    (p : Fin n → ℤ) (d : ℤ) (Q : ℕ) (hd : d≠0)
    (hdQ : |d|≤(Q : ℤ)) (hpQ : ∀ j, |p j|≤(Q : ℤ))
    (hx : ∀ j, x j=(p j : ℝ)/(d : ℝ)) :
    ∃ q : Fin n → ℤ, ∃ e : ℕ, 0<e ∧ e≤Q ∧
      (∀ j, |q j|≤(Q : ℤ)) ∧ ∀ j, x j=(q j : ℝ)/(e : ℝ) := by
  by_cases hpos : 0<d
  · refine ⟨p,d.toNat,?_,?_,hpQ,?_⟩
    · omega
    · have hdabs : |d|=d := abs_of_pos hpos
      rw [hdabs] at hdQ
      omega
    · intro j
      rw [hx j]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hpos)).symm
  · have hneg : d<0 := lt_of_le_of_ne (le_of_not_gt hpos) hd
    refine ⟨fun j => -p j,(-d).toNat,?_,?_,?_,?_⟩
    · omega
    · have hdabs : |d|= -d := abs_of_neg hneg
      rw [hdabs] at hdQ
      omega
    · intro j; simpa only [abs_neg] using hpQ j
    · intro j
      rw [hx j]
      have he : (((-d).toNat : ℕ) : ℝ)= -(d : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hneg)))
      rw [he,Int.cast_neg]
      exact (neg_div_neg_eq _ _).symm

#print axioms normalize_common_denominator
end IV04.Paper.InequalityCertificate
