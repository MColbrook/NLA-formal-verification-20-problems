module

public import NLA.IV04.PaperContinuantGrowthDefinitions
public import NLA.IV04.PaperRationalContinuant
public import NLA.IV04.PaperBinaryFractions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem common_denominator_continuant (n : ℕ) (a lower upper : ℕ → ℤ)
    (D : ℕ) (hD : 0 < D) :
    rationalContinuantValue (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D) n =
      (integerContinuantValue a lower upper n : ℚ)/(D : ℚ)^n := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  induction n using Nat.twoStepInduction with
  | zero => simp [rationalContinuantValue,integerContinuantValue]
  | one => simp [rationalContinuantValue,integerContinuantValue,commonDenominatorCoefficients]
  | more n hn hn1 =>
    rw [rationalContinuantValue,hn,hn1]
    simp only [integerContinuantValue,commonDenominatorCoefficients,
      Int.cast_sub,Int.cast_mul,pow_succ]
    field_simp [hDq]
    <;> ring

theorem common_denominator_determinant (n : ℕ) (a lower upper : ℕ → ℤ)
    (D : ℕ) (hD : 0 < D) :
    (rationalContinuantMatrix n (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D)).det =
      (integerContinuantValue a lower upper n : ℚ)/(D : ℚ)^n := by
  rw [rationalContinuantMatrix_det,common_denominator_continuant n a lower upper D hD]

theorem integer_continuant_magnitude (n : ℕ) (a lower upper : ℕ → ℤ)
    (H : ℕ) (hH : 1 ≤ H)
    (ha : ∀ i < n, (a i).natAbs ≤ H)
    (hl : ∀ i < n, (lower i).natAbs ≤ H)
    (hu : ∀ i < n, (upper i).natAbs ≤ H) :
    (integerContinuantValue a lower upper n).natAbs ≤ (2*H^2)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [integerContinuantValue]
  | one =>
    simpa [integerContinuantValue] using
      (ha 0 (by omega)).trans (by nlinarith : H ≤ 2*H^2)
  | more n hn hn1 =>
    have h0 := hn (fun i hi => ha i (by omega))
      (fun i hi => hl i (by omega)) (fun i hi => hu i (by omega))
    have h1 := hn1 (fun i hi => ha i (by omega))
      (fun i hi => hl i (by omega)) (fun i hi => hu i (by omega))
    have hdiag := ha (n+1) (by omega)
    have hlower := hl (n+1) (by omega)
    have hupper := hu n (by omega)
    have hH2 : H ≤ H^2 := by nlinarith
    calc
      (integerContinuantValue a lower upper (n+2)).natAbs ≤
          (a (n+1)).natAbs*(integerContinuantValue a lower upper (n+1)).natAbs+
          (lower (n+1)).natAbs*(upper n).natAbs*(integerContinuantValue a lower upper n).natAbs := by
        simpa only [integerContinuantValue,Int.natAbs_mul] using
          Int.natAbs_sub_le (a (n+1)*integerContinuantValue a lower upper (n+1))
            (lower (n+1)*upper n*integerContinuantValue a lower upper n)
      _ ≤ H*(2*H^2)^(n+1)+H^2*(2*H^2)^n := by
        exact Nat.add_le_add (Nat.mul_le_mul hdiag h1)
          (Nat.mul_le_mul (by nlinarith [Nat.mul_le_mul hlower hupper]) h0)
      _ ≤ (2*H^2)^(n+2) := by
        have hpos : 1 ≤ H^2 := by nlinarith
        have hc : H*(2*H^2)+H^2 ≤ (2*H^2)*(2*H^2) := by
          have hm := Nat.mul_le_mul_right (2*H^2) hH2
          have hm2 := Nat.mul_le_mul_right (H^2) hpos
          nlinarith
        calc
          H*(2*H^2)^(n+1)+H^2*(2*H^2)^n =
              (H*(2*H^2)+H^2)*(2*H^2)^n := by rw [pow_succ]; ring
          _ ≤ ((2*H^2)*(2*H^2))*(2*H^2)^n := Nat.mul_le_mul_right _ hc
          _ = (2*H^2)^(n+2) := by simp only [pow_succ]; ring

theorem integer_continuant_payload_bits (n : ℕ) (a lower upper : ℕ → ℤ)
    (B : ℕ)
    (ha : ∀ i < n, (a i).natAbs ≤ 2^B)
    (hl : ∀ i < n, (lower i).natAbs ≤ 2^B)
    (hu : ∀ i < n, (upper i).natAbs ≤ 2^B) :
    (integerContinuantValue a lower upper n).natAbs.size ≤ n*(2*B+1)+1 := by
  have hpow : 1 ≤ 2^B := by
    have hp : 0 < 2^B := by positivity
    omega
  have h := integer_continuant_magnitude n a lower upper (2^B) hpow ha hl hu
  have he : (2*(2^B)^2)^n = 2^(n*(2*B+1)) := by
    have hb : 2*(2^B)^2 = 2^(2*B+1) := by
      rw [← pow_mul,show B*2=2*B by omega,pow_succ]
      ring
    rw [hb,← pow_mul,Nat.mul_comm]
  rw [he] at h
  apply Nat.size_le.mpr
  have hp : 0 < 2^(n*(2*B+1)) := by positivity
  rw [pow_succ]
  omega

theorem rational_continuant_reduced_payload (n : ℕ) (a lower upper : ℕ → ℤ)
    (D : ℕ) (hD : 0 < D) :
    let q := rationalContinuantValue (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D) n
    q.num.natAbs ≤ (integerContinuantValue a lower upper n).natAbs ∧ q.den ≤ D^n := by
  dsimp only
  rw [common_denominator_continuant n a lower upper D hD]
  have hpos : 0 < D^n := by positivity
  simpa only [Nat.cast_pow] using
    IV04.Paper.reduced_fraction_payload (integerContinuantValue a lower upper n) (D^n) hpos

theorem rational_continuant_payload_bits (n : ℕ) (a lower upper : ℕ → ℤ)
    (D B C : ℕ) (hD : 0 < D) (hDb : D ≤ 2^C)
    (ha : ∀ i < n, (a i).natAbs ≤ 2^B)
    (hl : ∀ i < n, (lower i).natAbs ≤ 2^B)
    (hu : ∀ i < n, (upper i).natAbs ≤ 2^B) :
    let q := rationalContinuantValue (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D) n
    q.num.natAbs.size ≤ n*(2*B+1)+1 ∧ q.den.size ≤ n*C+1 := by
  dsimp only
  have h := rational_continuant_reduced_payload n a lower upper D hD
  dsimp only at h
  constructor
  · exact (Nat.size_le_size h.1).trans (integer_continuant_payload_bits n a lower upper B ha hl hu)
  · have hd : D^n ≤ 2^(n*C) := by
      simpa only [← pow_mul,Nat.mul_comm] using Nat.pow_le_pow_left hDb n
    have hs := Nat.size_le_size (h.2.trans hd)
    simpa only [Nat.size_pow] using hs

#print axioms rational_continuant_reduced_payload
end IV04.Paper.Computational
