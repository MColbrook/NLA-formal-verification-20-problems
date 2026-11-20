module

public import NLA.RA09.SpectralOptimality.RealLower

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace RootRA09SpectralOptimality
open NLA.RA09

theorem real_combination_mul {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v w : Fin n → ℝ) :
    spectralCombination d v * spectralCombination d w = spectralCombination d (fun i => v i*w i) := by
  let Q : RealMatrix n := d.orthogonal
  change (Q*Matrix.diagonal v*Q.transpose)*(Q*Matrix.diagonal w*Q.transpose) = _
  calc
    _ = Q*Matrix.diagonal v*(Q.transpose*Q)*Matrix.diagonal w*Q.transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [orthogonal_transpose_mul d.orthogonal,Matrix.mul_one,Matrix.mul_assoc Q,Matrix.diagonal_mul_diagonal]
      rfl

theorem real_combination_one {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) :
    spectralCombination d (fun _ => 1) = 1 := by
  simpa [spectralCombination] using orthogonal_mul_transpose d.orthogonal

theorem real_combination_smul {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (c : ℝ) (v : Fin n → ℝ) :
    spectralCombination d (fun i => c*v i) = c • spectralCombination d v := by
  have hd : Matrix.diagonal (fun i => c*v i) = c • Matrix.diagonal v := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,hij]
  simp only [spectralCombination,hd,Matrix.mul_smul,Matrix.smul_mul]

theorem real_combination_rank {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) : (spectralCombination d v).rank = (Matrix.diagonal v).rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · rw [← spectralCombination_conjugate d v]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem real_selected_rank {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (k : ℕ) :
    (spectralCombination d (fun i => if i.val < k then v i else 0)).rank ≤ k := by
  rw [real_combination_rank,Matrix.rank_diagonal]
  let e : {i : Fin n // (if i.val < k then v i else 0) ≠ 0} → Fin k :=
    fun i => ⟨i.val.val, by
      by_contra h
      have hi := i.property
      simp only [if_neg h, ne_self_iff_false] at hi⟩
  have hinj : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin k => z.val) h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e hinj

theorem actual_real_selected_rank {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (f : ℝ → ℝ) (k : ℕ) : (truncation d k).rank ≤ k ∧ (functionTruncation d f k).rank ≤ k :=
  ⟨real_selected_rank d d.eigenvalues k,real_selected_rank d (fun i => f (d.eigenvalues i)) k⟩

theorem actual_real_projector_rank {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (k : ℕ) (hk : k ≤ n) : (selectedProjector d k).rank = k := by
  rw [selectedProjector,real_combination_rank,Matrix.rank_diagonal]
  let e : {i : Fin n // (if i.val < k then (1 : ℝ) else 0) ≠ 0} ≃ Fin k :=
    { toFun := fun i => ⟨i.val.val, by
        by_contra h
        have hi := i.property
        simp only [if_neg h,ne_self_iff_false] at hi⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt hk⟩, by simp [j.isLt]⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  simpa only [Fintype.card_fin] using Fintype.card_congr e

theorem actual_real_projector_idempotent {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (k : ℕ) : selectedProjector d k * selectedProjector d k = selectedProjector d k := by
  rw [selectedProjector,real_combination_mul]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem actual_real_selected_action {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (f : ℝ → ℝ) (k : ℕ) :
    functionTruncation d f k = functionalCalculus f A * selectedProjector d k ∧
      functionTruncation d f k * (1-selectedProjector d k) = 0 := by
  have he : functionTruncation d f k = functionalCalculus f A * selectedProjector d k := by
    rw [selected_cfc_eq,selectedProjector,real_combination_mul]
    unfold functionTruncation
    congr 1
    funext i
    split_ifs <;> simp
  refine ⟨he, ?_⟩
  rw [he,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_assoc,actual_real_projector_idempotent,sub_self]

theorem actual_real_nullspace_action {n : ℕ} {B : RealMatrix n} (d : OrderedSpectralData B)
    (f : ℝ → ℝ) (k : ℕ) (hB : B.rank ≤ k) :
    functionalCalculus f B - functionTruncation d f k = f 0 • (1-selectedProjector d k) := by
  rw [selected_cfc_eq,functionTruncation,spectralCombination_sub]
  have he : (fun i : Fin n => f (d.eigenvalues i) - if i.val < k then f (d.eigenvalues i) else 0) =
      (fun i => f 0 * (1-if i.val < k then 1 else 0)) := by
    funext i
    by_cases hi : i.val < k
    · simp [hi]
    · simp [hi,Paper.eigenvalue_zero_of_rank_le d k hB i (Nat.le_of_not_gt hi)]
  rw [he,real_combination_smul,← spectralCombination_sub,real_combination_one]
  rfl

theorem actual_real_optimal_attainment {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (k : ℕ) (hk : k ≤ n) :
    (truncation d k).rank ≤ k ∧ frobeniusSquared (A-truncation d k) = spectralTail d k ∧
      (∀ B : RealMatrix n, B.rank ≤ k → spectralTail d k ≤ frobeniusSquared (A-B)) ∧
    (functionTruncation d f k).rank ≤ k ∧
      frobeniusSquared (functionalCalculus f A-functionTruncation d f k) = functionTail d f k ∧
      (∀ B : RealMatrix n, B.rank ≤ k → functionTail d f k ≤ frobeniusSquared (functionalCalculus f A-B)) := by
  have hs := truncation_semantics_proved d k hk f
  have hr := actual_real_selected_rank d f k
  exact ⟨hr.1,hs.2.2.1,fun B hB => actual_real_spectral_tail_lower d B k hB,
    hr.2,hs.2.2.2.1,fun B hB => actual_real_function_tail_lower d f hf B k hB⟩

#print axioms actual_real_optimal_attainment
#print axioms actual_real_nullspace_action
end RootRA09SpectralOptimality
