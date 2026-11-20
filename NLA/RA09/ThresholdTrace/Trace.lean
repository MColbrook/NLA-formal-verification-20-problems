module

public import NLA.RA09.ThresholdTrace.Scalar

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder
namespace RootRA09ThresholdTrace
open NLA.RA09

theorem outer_trace {n : ℕ} (v : Fin n → ℝ) (M : RealMatrix n) :
    (outerSquare v*M).trace = v ⬝ᵥ (M*ᵥv) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,outerSquare,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem eigenvector_quadratic {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (u : Fin n → ℝ) (j : Fin n) :
    eigenvector dB j ⬝ᵥ (spectralCombination dA u*ᵥeigenvector dB j) =
      ∑ i, overlapWeights dA dB i j*u i := by
  have h := spectralCombination_trace_product dA dB u (Pi.single j 1)
  rw [spectralCombination_single,one_smul,outer_trace] at h
  change ((fun i => (dB.orthogonal : RealMatrix n) i j) ⬝ᵥ
    (spectralCombination dA u*ᵥ(fun i => (dB.orthogonal : RealMatrix n) i j))) = _
  simpa only [eigenvector,Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using h

theorem actual_projector_trace {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (f : ℝ → ℝ) (τ : ℝ) (k : ℕ) :
    (selectedProjector dB k * functionalCalculus (thresholdAuxiliary f τ) A).trace =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
        ∑ i, overlapWeights dA dB i j*thresholdAuxiliary f τ (dA.eigenvalues i) := by
  rw [selected_cfc_eq dA,selectedProjector,spectralCombination_trace_product]
  simp only [Finset.sum_filter,ite_mul,one_mul,zero_mul]

theorem actual_projector_trace_bound {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (k : ℕ) (hk : k < n)
    (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    (selectedProjector dB k * functionalCalculus
      (thresholdAuxiliary f (dA.eigenvalues ⟨k,hk⟩)) A).trace ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        (2*(transferScale f (dA.eigenvalues ⟨k,hk⟩))^2*(dA.eigenvalues i)^2-
          (f (dA.eigenvalues i))^2) := by
  rw [actual_projector_trace dA dB f (dA.eigenvalues ⟨k,hk⟩) k]
  exact Paper.unordered_auxiliary_average dA dB f hf k hk hτ

theorem projector_average_positive {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (τ : ℝ) (hτ : 0 < τ)
    (hfτ : 0 < f τ) (k : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
      ((f (dB.eigenvalues j))^2-2*(transferScale f τ)^2*(dB.eigenvalues j)^2-
        2*f (dB.eigenvalues j)*(eigenvector dB j ⬝ᵥ (functionalCalculus f A*ᵥeigenvector dB j))+
        4*(transferScale f τ)^2*dB.eigenvalues j*(eigenvector dB j ⬝ᵥ (A*ᵥeigenvector dB j)))) ≤
      (selectedProjector dB k * functionalCalculus (thresholdAuxiliary f τ) A).trace := by
  rw [actual_projector_trace dA dB f τ k]
  apply Finset.sum_le_sum
  intro j _
  have hA : A = spectralCombination dA dA.eigenvalues := dA.reconstruct
  have hAq : eigenvector dB j ⬝ᵥ (A*ᵥeigenvector dB j) =
      ∑ i, overlapWeights dA dB i j*dA.eigenvalues i := by
    calc
      _ = eigenvector dB j ⬝ᵥ (spectralCombination dA dA.eigenvalues*ᵥeigenvector dB j) :=
        congrArg (fun M : RealMatrix n => eigenvector dB j ⬝ᵥ (M*ᵥeigenvector dB j)) hA
      _ = _ := eigenvector_quadratic dA dB dA.eigenvalues j
  rw [selected_cfc_eq dA,eigenvector_quadratic dA dB (fun i => f (dA.eigenvalues i)) j,hAq]
  exact Paper.unordered_column_average dA dB f hf τ hτ hfτ j

theorem actual_projector_average {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (τ : ℝ) (hτ : 0 < τ) (k : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
      ((f (dB.eigenvalues j))^2-2*(transferScale f τ)^2*(dB.eigenvalues j)^2-
        2*f (dB.eigenvalues j)*(eigenvector dB j ⬝ᵥ (functionalCalculus f A*ᵥeigenvector dB j))+
        4*(transferScale f τ)^2*dB.eigenvalues j*(eigenvector dB j ⬝ᵥ (A*ᵥeigenvector dB j)))) ≤
      (selectedProjector dB k * functionalCalculus (thresholdAuxiliary f τ) A).trace := by
  by_cases hz : f τ = 0
  · have hzero := (Paper.admissible_scalar_consequences_proved f hf τ hτ).2.2.2.2.2 hz
    have hA : ∀ i, f (dA.eigenvalues i) = 0 := fun i => hzero _ (dA.nonnegative i)
    have hB : ∀ i, f (dB.eigenvalues i) = 0 := fun i => hzero _ (dB.nonnegative i)
    rw [actual_projector_trace dA dB f τ k]
    simp only [hA,hB,transferScale,hz,zero_div,thresholdAuxiliary]
    norm_num
  · exact projector_average_positive dA dB f hf τ hτ
      (lt_of_le_of_ne (hf.2.2.1 τ hτ.le) (Ne.symm hz)) k

theorem actual_threshold_spectral_data {n : ℕ} {A : RealMatrix n}
    (dA : OrderedSpectralData A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ dH : OrderedSpectralData (functionalCalculus (thresholdAuxiliary f τ) A),
      dH.eigenvalues = (fun i => thresholdAuxiliary f τ (dA.eigenvalues i)) ∧
        dH.orthogonal = dA.orthogonal := by
  refine ⟨{
    eigenvalues := fun i => thresholdAuxiliary f τ (dA.eigenvalues i)
    orthogonal := dA.orthogonal
    decreasing := actual_ordered_threshold_values dA f hf τ hτ
    nonnegative := fun i => (sq_nonneg (f τ)).trans (le_max_right _ _)
    reconstruct := selected_cfc_eq dA (thresholdAuxiliary f τ)
  },rfl,rfl⟩

theorem actual_projector_structure {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (hk : k ≤ n) :
    selectedProjector d k = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), outerSquare (eigenvector d j) ∧
      (selectedProjector d k).PosSemidef ∧
      selectedProjector d k * selectedProjector d k = selectedProjector d k ∧
      (selectedProjector d k).rank = k := by
  have hsum : selectedProjector d k = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), outerSquare (eigenvector d j) := by
    ext i l
    simp only [selectedProjector,spectralCombination_entry,Matrix.sum_apply,Finset.sum_filter,outerSquare,eigenvector]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hpsd : (selectedProjector d k).PosSemidef := by
    apply spectralCombination_posSemidef
    intro i
    split_ifs <;> norm_num
  have hmul : selectedProjector d k * selectedProjector d k = selectedProjector d k := by
    let Q : RealMatrix n := d.orthogonal
    let D : RealMatrix n := Matrix.diagonal (fun i : Fin n => if i.val < k then 1 else 0)
    have hD : D*D = D := by
      dsimp only [D]
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> norm_num
    change (Q*D*Q.transpose)*(Q*D*Q.transpose)=Q*D*Q.transpose
    calc
      _ = Q*D*(Q.transpose*Q)*D*Q.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [orthogonal_transpose_mul d.orthogonal,Matrix.mul_one,Matrix.mul_assoc Q,hD]
  have hrank (v : Fin n → ℝ) : (spectralCombination d v).rank = (Matrix.diagonal v).rank := by
    apply le_antisymm
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · rw [← spectralCombination_conjugate d v]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  refine ⟨hsum,hpsd,hmul,?_⟩
  rw [selectedProjector,hrank,Matrix.rank_diagonal]
  let e : {i : Fin n // (if i.val < k then (1 : ℝ) else 0) ≠ 0} ≃ Fin k :=
    { toFun := fun i => ⟨i.val.val, by
        by_contra h
        have hi := i.property
        simp only [if_neg h,ne_self_iff_false] at hi⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt hk⟩, by simp [j.isLt]⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  simpa only [Fintype.card_fin] using Fintype.card_congr e

#print axioms actual_projector_trace
#print axioms actual_projector_trace_bound
#print axioms actual_projector_average
end RootRA09ThresholdTrace
