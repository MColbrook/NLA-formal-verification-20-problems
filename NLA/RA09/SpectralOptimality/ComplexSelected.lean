module

public import NLA.RA09.SpectralOptimality.ComplexLower

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace RootRA09SpectralOptimality
open NLA.RA09.ComplexPaper

theorem complex_combination_mul {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v w : Fin n → ℝ) :
    spectralCombination d v * spectralCombination d w = spectralCombination d (fun i => v i*w i) := by
  let Q : ComplexMatrix n := d.unitary
  change (Q*Matrix.diagonal (fun i => (v i : ℂ))*Q.conjTranspose)*
    (Q*Matrix.diagonal (fun i => (w i : ℂ))*Q.conjTranspose) = _
  calc
    _ = Q*Matrix.diagonal (fun i => (v i : ℂ))*(Q.conjTranspose*Q)*
        Matrix.diagonal (fun i => (w i : ℂ))*Q.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [unitary_star_mul d.unitary,Matrix.mul_one,Matrix.mul_assoc Q,Matrix.diagonal_mul_diagonal]
      simp only [spectralCombination,Q,Complex.ofReal_mul]

theorem complex_combination_one {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    spectralCombination d (fun _ => 1) = 1 := by
  simpa [spectralCombination] using unitary_mul_star d.unitary

theorem complex_combination_smul {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (c : ℝ) (v : Fin n → ℝ) :
    spectralCombination d (fun i => c*v i) = c • spectralCombination d v := by
  have hd : Matrix.diagonal (fun i => ((c*v i : ℝ) : ℂ)) = c • Matrix.diagonal (fun i => (v i : ℂ)) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,hij,Complex.real_smul]
  simp only [spectralCombination,hd,Matrix.mul_smul,Matrix.smul_mul]

theorem complex_combination_rank {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) :
    (spectralCombination d v).rank = (Matrix.diagonal (fun i => (v i : ℂ))).rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · rw [← spectralCombination_conjugate d v]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem complex_selected_rank {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (k : ℕ) :
    (spectralCombination d (fun i => if i.val < k then v i else 0)).rank ≤ k := by
  rw [complex_combination_rank,Matrix.rank_diagonal]
  let e : {i : Fin n // ((if i.val < k then v i else 0 : ℝ) : ℂ) ≠ 0} → Fin k :=
    fun i => ⟨i.val.val, by
      by_contra h
      have hi := i.property
      simp only [if_neg h, Complex.ofReal_zero, ne_self_iff_false] at hi⟩
  have hinj : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin k => z.val) h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e hinj

theorem actual_complex_selected_rank {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (f : ℝ → ℝ) (k : ℕ) : (truncation d k).rank ≤ k ∧ (functionTruncation d f k).rank ≤ k :=
  ⟨complex_selected_rank d d.eigenvalues k,complex_selected_rank d (fun i => f (d.eigenvalues i)) k⟩

theorem actual_complex_projector_rank {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (k : ℕ) (hk : k ≤ n) : (complexSelectedProjector d k).rank = k := by
  rw [complexSelectedProjector,complex_combination_rank,Matrix.rank_diagonal]
  let e : {i : Fin n // ((if i.val < k then (1 : ℝ) else 0) : ℂ) ≠ 0} ≃ Fin k :=
    { toFun := fun i => ⟨i.val.val, by
        by_contra h
        have hi := i.property
        simp only [if_neg h,Complex.ofReal_zero,ne_self_iff_false] at hi⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt hk⟩, by simp [j.isLt]⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  simpa only [Fintype.card_fin, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using Fintype.card_congr e

theorem actual_complex_projector_idempotent {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (k : ℕ) : complexSelectedProjector d k * complexSelectedProjector d k = complexSelectedProjector d k := by
  rw [complexSelectedProjector,complex_combination_mul]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem actual_complex_selected_action {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (f : ℝ → ℝ) (k : ℕ) :
    functionTruncation d f k = functionalCalculus f A * complexSelectedProjector d k ∧
      functionTruncation d f k * (1-complexSelectedProjector d k) = 0 := by
  have he : functionTruncation d f k = functionalCalculus f A * complexSelectedProjector d k := by
    rw [selected_cfc_eq,complexSelectedProjector,complex_combination_mul]
    unfold functionTruncation
    congr 1
    funext i
    split_ifs <;> simp
  refine ⟨he, ?_⟩
  rw [he,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_assoc,actual_complex_projector_idempotent,sub_self]

theorem actual_complex_nullspace_action {n : ℕ} {B : ComplexMatrix n} (d : OrderedSpectralData B)
    (f : ℝ → ℝ) (k : ℕ) (hB : B.rank ≤ k) :
    functionalCalculus f B - functionTruncation d f k = f 0 • (1-complexSelectedProjector d k) := by
  rw [selected_cfc_eq,functionTruncation,spectralCombination_sub]
  have he : (fun i : Fin n => f (d.eigenvalues i) - if i.val < k then f (d.eigenvalues i) else 0) =
      (fun i => f 0 * (1-if i.val < k then 1 else 0)) := by
    funext i
    by_cases hi : i.val < k
    · simp [hi]
    · simp [hi,eigenvalue_zero_of_rank_le d k hB i (Nat.le_of_not_gt hi)]
  rw [he,complex_combination_smul,← spectralCombination_sub,complex_combination_one]
  rfl

theorem actual_complex_optimal_attainment {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (f : ℝ → ℝ) (hf : NLA.RA09.PaperAdmissibleFunction f) (k : ℕ) (hk : k ≤ n) :
    (truncation d k).rank ≤ k ∧ frobeniusSquared (A-truncation d k) = spectralTail d k ∧
      (∀ B : ComplexMatrix n, B.rank ≤ k → spectralTail d k ≤ frobeniusSquared (A-B)) ∧
    (functionTruncation d f k).rank ≤ k ∧
      frobeniusSquared (functionalCalculus f A-functionTruncation d f k) = functionTail d f k ∧
      (∀ B : ComplexMatrix n, B.rank ≤ k → functionTail d f k ≤ frobeniusSquared (functionalCalculus f A-B)) := by
  have hs := truncation_semantics_proved d k hk f
  have hr := actual_complex_selected_rank d f k
  exact ⟨hr.1,hs.2.2.1,fun B hB => actual_complex_spectral_tail_lower d B k hB,
    hr.2,hs.2.2.2.1,fun B hB => actual_complex_function_tail_lower d f hf B k hB⟩

#print axioms actual_complex_optimal_attainment
#print axioms actual_complex_nullspace_action
end RootRA09SpectralOptimality
