module

public import NLA.RA09.Paper.Unordered
public import NLA.RA09.Paper.Weights

@[expose] public section

/-! Unordered matrix transfer from the exact scalar certificate and actual
orthogonal eigenvector overlaps. Mathematical argument: Matthew J. Colbrook.
AI-assisted Lean formalization. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder
namespace NLA.RA09.Paper

theorem unordered_column_average {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) (hfτ : 0 < f τ) (j : Fin n) :
    (f (dB.eigenvalues j))^2 - 2*(transferScale f τ)^2*(dB.eigenvalues j)^2 -
      2*f (dB.eigenvalues j)*(∑ i, overlapWeights dA dB i j*f (dA.eigenvalues i)) +
      4*(transferScale f τ)^2*dB.eigenvalues j*
        (∑ i, overlapWeights dA dB i j*dA.eigenvalues i) ≤
    ∑ i, overlapWeights dA dB i j*unorderedAuxiliary f τ (dA.eigenvalues i) := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left
      (unordered_scalar_scaled f hf τ (dA.eigenvalues i) (dB.eigenvalues j)
        hτ hfτ (dA.nonnegative i) (dB.nonnegative j))
      (sq_nonneg (overlapMatrix dA dB i j))
  have hid : (∑ i, overlapWeights dA dB i j *
      ((f (dB.eigenvalues j))^2 - 2*f (dB.eigenvalues j)*f (dA.eigenvalues i) -
        2*(transferScale f τ)^2*(dB.eigenvalues j)^2 +
        4*(transferScale f τ)^2*dA.eigenvalues i*dB.eigenvalues j)) =
      (f (dB.eigenvalues j))^2 - 2*(transferScale f τ)^2*(dB.eigenvalues j)^2 -
        2*f (dB.eigenvalues j)*(∑ i, overlapWeights dA dB i j*f (dA.eigenvalues i)) +
        4*(transferScale f τ)^2*dB.eigenvalues j*
          (∑ i, overlapWeights dA dB i j*dA.eigenvalues i) := by
    calc
      _ = ∑ i, ((f (dB.eigenvalues j))^2*overlapWeights dA dB i j -
          (2*f (dB.eigenvalues j))*(overlapWeights dA dB i j*f (dA.eigenvalues i)) -
          (2*(transferScale f τ)^2*(dB.eigenvalues j)^2)*overlapWeights dA dB i j +
          (4*(transferScale f τ)^2*dB.eigenvalues j)*
            (overlapWeights dA dB i j*dA.eigenvalues i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          overlap_column_sum, mul_one]
        ring
  simp only [overlapWeights] at hid ⊢
  rwa [hid] at h

theorem unordered_auxiliary_average {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
      ∑ i, overlapWeights dA dB i j *
        unorderedAuxiliary f (dA.eigenvalues ⟨k,hk⟩) (dA.eigenvalues i)) ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
      (2*(transferScale f (dA.eigenvalues ⟨k,hk⟩))^2*(dA.eigenvalues i)^2 -
        (f (dA.eigenvalues i))^2) := by
  let S := Finset.univ.filter (fun i : Fin n => i.val < k)
  let τ := dA.eigenvalues ⟨k,hk⟩
  have h := selected_average_bound S (overlapWeights dA dB)
    (fun i => unorderedAuxiliary f τ (dA.eigenvalues i)) ((f τ)^2)
    (overlap_column_sum dA dB) (fun i => ?_) (fun i _ => le_max_right _ _)
    (fun i hi => ?_)
  · apply h.trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    exact (unordered_auxiliary_cutoff f hf τ hτ).2 _
      (dA.decreasing (show i ≤ ⟨k,hk⟩ from Nat.le_of_lt (Finset.mem_filter.mp hi).2))
  · calc
      _ ≤ ∑ j, overlapWeights dA dB i j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => sq_nonneg _)
      _ = 1 := overlap_row_sum dA dB i
  · have hi' : k ≤ i.val := by simpa [S, not_lt] using hi
    exact (unordered_auxiliary_cutoff f hf τ hτ).1 _ (dA.nonnegative i)
      (dA.decreasing (show (⟨k,hk⟩ : Fin n) ≤ i from hi'))

theorem unordered_overlap_identity {n : ℕ} (a b F G : Fin n → ℝ)
    (p : Fin n → Fin n → ℝ) (c : ℝ) (S : Finset (Fin n)) :
    ((∑ i, F i^2) + (∑ j ∈ S, G j^2) -
        2 * ∑ j ∈ S, G j * (∑ i, p i j * F i)) -
      2*c^2 * ((∑ i, a i^2) + (∑ j ∈ S, b j^2) -
        2 * ∑ j ∈ S, b j * (∑ i, p i j * a i)) =
    (∑ i, (F i^2-2*c^2*a i^2)) +
      ∑ j ∈ S, (G j^2-2*c^2*b j^2 - 2*G j*(∑ i, p i j*F i) +
        4*c^2*b j*(∑ i, p i j*a i)) := by
  simp only [mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem unordered_tail_identity {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (c : ℝ) (k : ℕ) :
    (∑ i, ((f (d.eigenvalues i))^2 - 2*c^2*(d.eigenvalues i)^2)) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        (2*c^2*(d.eigenvalues i)^2 - (f (d.eigenvalues i))^2)) =
    functionTail d f k - 2*c^2*spectralTail d k := by
  unfold functionTail spectralTail
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k
  · simp [hi, Nat.not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi]

theorem unordered_positive_tail_transfer {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) -
      functionTail dA f k ≤
    2*(transferScale f (dA.eigenvalues ⟨k,hk⟩))^2 *
      (frobeniusSquared (A - truncation dB k) - spectralTail dA k) := by
  let τ := dA.eigenvalues ⟨k,hk⟩
  by_cases hfτ : f τ = 0
  · have hz := (admissible_scalar_consequences_proved f hf τ hτ).2.2.2.2.2 hfτ
    have hfa : ∀ i, f (dA.eigenvalues i) = 0 := fun i => hz _ (dA.nonnegative i)
    have hfb : ∀ i, f (dB.eigenvalues i) = 0 := fun i => hz _ (dB.nonnegative i)
    rw [(overlap_error_expansions_proved dA dB f k hk.le).2]
    change _ ≤ 2*(transferScale f τ)^2*_
    simp only [hfa, hfb, transferScale, hfτ, zero_div, functionTail,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, Finset.sum_const_zero,
      add_zero, sub_zero, le_refl]
  · have hfτpos : 0 < f τ := lt_of_le_of_ne (hf.2.2.1 τ hτ.le) (Ne.symm hfτ)
    have hbound :
        frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) -
          2*(transferScale f τ)^2*frobeniusSquared (A - truncation dB k) ≤
        functionTail dA f k - 2*(transferScale f τ)^2*spectralTail dA k := by
      obtain ⟨hA,hF⟩ := overlap_error_expansions_proved dA dB f k hk.le
      rw [hA, hF, unordered_overlap_identity dA.eigenvalues dB.eigenvalues
        (fun i => f (dA.eigenvalues i)) (fun j => f (dB.eigenvalues j))
        (fun i j => overlapWeights dA dB i j) (transferScale f τ)
        (Finset.univ.filter (fun j : Fin n => j.val < k))]
      rw [← unordered_tail_identity dA f (transferScale f τ) k]
      apply add_le_add le_rfl
      calc
        _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
            ∑ i, overlapWeights dA dB i j*unorderedAuxiliary f τ (dA.eigenvalues i) :=
          Finset.sum_le_sum fun j _ => unordered_column_average dA dB f hf τ hτ hfτpos j
        _ ≤ _ := unordered_auxiliary_average dA dB f hf k hk hτ
    change _ ≤ 2*(transferScale f τ)^2*_
    nlinarith

#print axioms unordered_positive_tail_transfer

end NLA.RA09.Paper
