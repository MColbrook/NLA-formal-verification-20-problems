module

public import NLA.RA09.ThresholdComplex.Definitions
public import NLA.RA09.ThresholdTrace.Solution
public import NLA.RA09.ComplexUnordered

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder ComplexOrder
namespace RootRA09ThresholdComplex
open NLA.RA09.ComplexPaper
open NLA.RA09 (PaperAdmissibleFunction transferScale)
open RootRA09ThresholdTrace (thresholdAuxiliary)

theorem outer_trace {n : ℕ} (v : Fin n → ℂ) (M : ComplexMatrix n) :
    (outerSquare v*M).trace = star v ⬝ᵥ (M*ᵥv) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,outerSquare,Matrix.vecMulVec_apply,
    Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spectral_single {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) (j : Fin n) :
    spectralCombination d (Pi.single j 1) = outerSquare (eigenvector d j) := by
  ext i l
  rw [spectralCombination_entry]
  simp [Pi.single_apply,outerSquare,eigenvector,Matrix.vecMulVec_apply,Pi.star_apply,apply_ite]

theorem eigenvector_quadratic {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (u : Fin n → ℝ) (j : Fin n) :
    star (eigenvector dB j) ⬝ᵥ (spectralCombination dA u*ᵥeigenvector dB j) =
      ((∑ i, overlapWeights dA dB i j*u i : ℝ) : ℂ) := by
  have h := spectralCombination_trace_product dA dB u (Pi.single j 1)
  rw [spectral_single,outer_trace] at h
  simpa only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using h

theorem actual_complex_projector_trace {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (f : ℝ → ℝ) (τ : ℝ) (k : ℕ) :
    (selectedProjector dB k * functionalCalculus (thresholdAuxiliary f τ) A).trace =
      ((∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
        ∑ i, overlapWeights dA dB i j*thresholdAuxiliary f τ (dA.eigenvalues i) : ℝ) : ℂ) := by
  rw [selected_cfc_eq dA,selectedProjector,spectralCombination_trace_product]
  simp only [Finset.sum_filter,ite_mul,one_mul,zero_mul]

theorem actual_complex_quadratic {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (f : ℝ → ℝ) (j : Fin n) :
    star (eigenvector dB j) ⬝ᵥ (functionalCalculus f A*ᵥeigenvector dB j) =
      ((∑ i, overlapWeights dA dB i j*f (dA.eigenvalues i) : ℝ) : ℂ) := by
  rw [selected_cfc_eq dA]
  exact eigenvector_quadratic dA dB (fun i => f (dA.eigenvalues i)) j

theorem actual_complex_projector_trace_bound {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (k : ℕ) (hk : k < n)
    (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    (selectedProjector dB k * functionalCalculus
      (thresholdAuxiliary f (dA.eigenvalues ⟨k,hk⟩)) A).trace.re ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        (2*(transferScale f (dA.eigenvalues ⟨k,hk⟩))^2*(dA.eigenvalues i)^2-
          (f (dA.eigenvalues i))^2) := by
  rw [actual_complex_projector_trace dA dB f (dA.eigenvalues ⟨k,hk⟩) k,Complex.ofReal_re]
  exact unordered_auxiliary_average dA dB f hf k hk hτ

theorem actual_complex_projector_average {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (τ : ℝ) (hτ : 0 < τ) (k : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
      ((f (dB.eigenvalues j))^2-2*(transferScale f τ)^2*(dB.eigenvalues j)^2-
        2*f (dB.eigenvalues j)*(star (eigenvector dB j) ⬝ᵥ (functionalCalculus f A*ᵥeigenvector dB j)).re+
        4*(transferScale f τ)^2*dB.eigenvalues j*(star (eigenvector dB j) ⬝ᵥ (A*ᵥeigenvector dB j)).re)) ≤
      (selectedProjector dB k * functionalCalculus (thresholdAuxiliary f τ) A).trace.re := by
  rw [actual_complex_projector_trace dA dB f τ k,Complex.ofReal_re]
  by_cases hz : f τ = 0
  · have hzero := (NLA.RA09.Paper.admissible_scalar_consequences_proved f hf τ hτ).2.2.2.2.2 hz
    have hA : ∀ i, f (dA.eigenvalues i) = 0 := fun i => hzero _ (dA.nonnegative i)
    have hB : ∀ i, f (dB.eigenvalues i) = 0 := fun i => hzero _ (dB.nonnegative i)
    simp only [hA,hB,transferScale,hz,zero_div,thresholdAuxiliary]
    norm_num
  · have hfτ : 0 < f τ := lt_of_le_of_ne (hf.2.2.1 τ hτ.le) (Ne.symm hz)
    apply Finset.sum_le_sum
    intro j _
    have hAq : star (eigenvector dB j) ⬝ᵥ (A*ᵥeigenvector dB j) =
        ((∑ i, overlapWeights dA dB i j*dA.eigenvalues i : ℝ) : ℂ) := by
      calc
        _ = star (eigenvector dB j) ⬝ᵥ (spectralCombination dA dA.eigenvalues*ᵥeigenvector dB j) :=
          congrArg (fun M : ComplexMatrix n => star (eigenvector dB j) ⬝ᵥ (M*ᵥeigenvector dB j)) dA.reconstruct
        _ = _ := eigenvector_quadratic dA dB dA.eigenvalues j
    rw [selected_cfc_eq dA,eigenvector_quadratic dA dB (fun i => f (dA.eigenvalues i)) j,hAq,
      Complex.ofReal_re,Complex.ofReal_re]
    exact unordered_column_average dA dB f hf τ hτ hfτ j

theorem actual_complex_threshold_spectral_data {n : ℕ} {A : ComplexMatrix n}
    (dA : OrderedSpectralData A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ dH : OrderedSpectralData (functionalCalculus (thresholdAuxiliary f τ) A),
      dH.eigenvalues = (fun i => thresholdAuxiliary f τ (dA.eigenvalues i)) ∧
        dH.unitary = dA.unitary := by
  refine ⟨{
    eigenvalues := fun i => thresholdAuxiliary f τ (dA.eigenvalues i)
    unitary := dA.unitary
    decreasing := fun i j hij => (RootRA09ThresholdTrace.actual_threshold_scalar f hf τ hτ).2.2.2
      (dA.nonnegative j) (dA.nonnegative i) (dA.decreasing hij)
    nonnegative := fun i => (sq_nonneg (f τ)).trans (le_max_right _ _)
    reconstruct := selected_cfc_eq dA (thresholdAuxiliary f τ)
  },rfl,rfl⟩

theorem actual_complex_projector_structure {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (hk : k ≤ n) :
    selectedProjector d k = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), outerSquare (eigenvector d j) ∧
      (selectedProjector d k).PosSemidef ∧
      selectedProjector d k * selectedProjector d k = selectedProjector d k ∧
      (selectedProjector d k).rank = k := by
  have hsum : selectedProjector d k = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), outerSquare (eigenvector d j) := by
    ext i l
    simp only [selectedProjector,spectralCombination_entry,Matrix.sum_apply,Finset.sum_filter,outerSquare,eigenvector,
      Matrix.vecMulVec_apply,Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hpsd : (selectedProjector d k).PosSemidef := by
    apply spectralCombination_posSemidef
    intro i
    split_ifs <;> norm_num
  have hmul : selectedProjector d k * selectedProjector d k = selectedProjector d k := by
    let Q : ComplexMatrix n := d.unitary
    let D : ComplexMatrix n := Matrix.diagonal (fun i : Fin n => ((if i.val < k then 1 else 0 : ℝ) : ℂ))
    have hD : D*D = D := by
      dsimp only [D]
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> norm_num
    change (Q*D*Q.conjTranspose)*(Q*D*Q.conjTranspose)=Q*D*Q.conjTranspose
    calc
      _ = Q*D*(Q.conjTranspose*Q)*D*Q.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [unitary_star_mul d.unitary,Matrix.mul_one,Matrix.mul_assoc Q,hD]
  have hrank (v : Fin n → ℝ) : (spectralCombination d v).rank = (Matrix.diagonal (fun i => (v i : ℂ))).rank := by
    apply le_antisymm
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · rw [← spectralCombination_conjugate d v]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  refine ⟨hsum,hpsd,hmul,?_⟩
  rw [selectedProjector,hrank,Matrix.rank_diagonal]
  let e : {i : Fin n // ((if i.val < k then (1 : ℝ) else 0) : ℂ) ≠ 0} ≃ Fin k :=
    { toFun := fun i => ⟨i.val.val, by
        by_contra h
        have hi := i.property
        simp only [if_neg h,ne_self_iff_false] at hi⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt hk⟩, by simp [j.isLt]⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  simpa only [Fintype.card_fin,apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using Fintype.card_congr e

#print axioms actual_complex_projector_average
#print axioms actual_complex_projector_structure
end RootRA09ThresholdComplex
