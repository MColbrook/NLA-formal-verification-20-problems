module

/- Honest determinant bounds for an integer Gram system and its Cramer numerators. -/
public import NLA.IV04.AffinePolyhedronSteps.RationalVertex
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

def gramCertificateBound (m n H : ℕ) : ℕ := n.factorial*(m*H^2)^n

theorem integer_det_entry_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (K : ℕ) (hB : ∀ i j, |B i j| ≤ (K : ℤ)) :
    |B.det| ≤ (n.factorial : ℤ)*(K : ℤ)^n := by
  simpa using (Matrix.det_le (abv:=AbsoluteValue.abs) hB)

theorem integer_gram_entry_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (M : Matrix ι (Fin n) ℤ) (H : ℕ)
    (hM : ∀ i j, |M i j| ≤ (H : ℤ)) (i j : Fin n) :
    |(Mᵀ*M) i j| ≤ (Fintype.card ι : ℤ)*(H : ℤ)^2 := by
  classical
  change |∑ k, M k i*M k j| ≤ _
  calc
    _ ≤ ∑ k, |M k i*M k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, (H : ℤ)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul,pow_two]
      exact mul_le_mul (hM k i) (hM k j) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by simp

theorem integer_gram_rhs_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (M : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (H : ℕ)
    (hM : ∀ i j, |M i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ)) (j : Fin n) :
    |(Mᵀ *ᵥ b) j| ≤ (Fintype.card ι : ℤ)*(H : ℤ)^2 := by
  classical
  change |∑ k, M k j*b k| ≤ _
  calc
    _ ≤ ∑ k, |M k j*b k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, (H : ℤ)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul,pow_two]
      exact mul_le_mul (hM k j) (hb k) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by simp

theorem integer_gram_cramer_bounds {ι : Type*} [Fintype ι] {n : ℕ}
    (M : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (H : ℕ)
    (hM : ∀ i j, |M i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ)) :
    |(Mᵀ*M).det| ≤ (gramCertificateBound (Fintype.card ι) n H : ℤ) ∧
    ∀ j, |((Mᵀ*M).updateCol j (Mᵀ *ᵥ b)).det| ≤
      (gramCertificateBound (Fintype.card ι) n H : ℤ) := by
  classical
  have hK (i j : Fin n) : |(Mᵀ*M) i j| ≤ ((Fintype.card ι*H^2 : ℕ) : ℤ) := by
    simpa using integer_gram_entry_bound M H hM i j
  have hc (i : Fin n) : |(Mᵀ *ᵥ b) i| ≤ ((Fintype.card ι*H^2 : ℕ) : ℤ) := by
    simpa using integer_gram_rhs_bound M b H hM hb i
  constructor
  · simpa [gramCertificateBound] using integer_det_entry_bound (Mᵀ*M) _ hK
  · intro j
    apply (integer_det_entry_bound _ (Fintype.card ι*H^2) ?_).trans_eq
      (by simp [gramCertificateBound])
    intro i k
    by_cases h : k=j
    · subst k
      simpa using hc i
    · simpa [Matrix.updateCol,h] using hK i k

#print axioms integer_det_entry_bound
#print axioms integer_gram_entry_bound
#print axioms integer_gram_rhs_bound
#print axioms integer_gram_cramer_bounds
end
end Reference.IV04AffinePolyhedronSteps
