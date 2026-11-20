module

public import NLA.RA09.ThresholdTrace.Trace

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder ComplexOrder
namespace RootRA09ThresholdTrace.Interface

section
open NLA.RA09
theorem actual_squared_difference (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ x y : ℝ) (hτ : 0 < τ) (htx : τ ≤ x) (hxy : x ≤ y) :
    (f y)^2-(f x)^2 ≤ (transferScale f τ)^2*(y^2-x^2) := by
  exact RootRA09ThresholdTrace.actual_squared_difference f hf τ x y hτ htx hxy
end

section
open NLA.RA09
theorem actual_threshold_scalar (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    (∀ a : ℝ, 0 ≤ a → a ≤ τ → thresholdAuxiliary f τ a = (f τ)^2) ∧
      (∀ a : ℝ, τ ≤ a → thresholdAuxiliary f τ a = 2*(transferScale f τ)^2*a^2-(f a)^2) ∧
      thresholdAuxiliary f τ τ = (f τ)^2 ∧
      MonotoneOn (thresholdAuxiliary f τ) (Set.Ici 0) := by
  exact RootRA09ThresholdTrace.actual_threshold_scalar f hf τ hτ
end

section
open NLA.RA09
theorem actual_ordered_threshold_values {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    Antitone (fun i => thresholdAuxiliary f τ (d.eigenvalues i)) := by
  exact RootRA09ThresholdTrace.actual_ordered_threshold_values d f hf τ hτ
end

section
open NLA.RA09
theorem actual_projector_trace {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (f : ℝ → ℝ) (τ : ℝ) (k : ℕ) :
    (selectedProjector dB k * functionalCalculus (thresholdAuxiliary f τ) A).trace =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
        ∑ i, overlapWeights dA dB i j*thresholdAuxiliary f τ (dA.eigenvalues i) := by
  exact RootRA09ThresholdTrace.actual_projector_trace dA dB f τ k
end

section
open NLA.RA09
theorem actual_projector_trace_bound {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (k : ℕ) (hk : k < n)
    (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    (selectedProjector dB k * functionalCalculus
      (thresholdAuxiliary f (dA.eigenvalues ⟨k,hk⟩)) A).trace ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        (2*(transferScale f (dA.eigenvalues ⟨k,hk⟩))^2*(dA.eigenvalues i)^2-
          (f (dA.eigenvalues i))^2) := by
  exact RootRA09ThresholdTrace.actual_projector_trace_bound dA dB f hf k hk hτ
end

section
open NLA.RA09
theorem actual_projector_average {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (τ : ℝ) (hτ : 0 < τ) (k : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
      ((f (dB.eigenvalues j))^2-2*(transferScale f τ)^2*(dB.eigenvalues j)^2-
        2*f (dB.eigenvalues j)*(eigenvector dB j ⬝ᵥ (functionalCalculus f A*ᵥeigenvector dB j))+
        4*(transferScale f τ)^2*dB.eigenvalues j*(eigenvector dB j ⬝ᵥ (A*ᵥeigenvector dB j)))) ≤
      (selectedProjector dB k * functionalCalculus (thresholdAuxiliary f τ) A).trace := by
  exact RootRA09ThresholdTrace.actual_projector_average dA dB f hf τ hτ k
end

section
open NLA.RA09
theorem actual_threshold_spectral_data {n : ℕ} {A : RealMatrix n}
    (dA : OrderedSpectralData A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ dH : OrderedSpectralData (functionalCalculus (thresholdAuxiliary f τ) A),
      dH.eigenvalues = (fun i => thresholdAuxiliary f τ (dA.eigenvalues i)) ∧
        dH.orthogonal = dA.orthogonal := by
  exact RootRA09ThresholdTrace.actual_threshold_spectral_data dA f hf τ hτ
end

section
open NLA.RA09
theorem actual_projector_structure {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (hk : k ≤ n) :
    selectedProjector d k = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), outerSquare (eigenvector d j) ∧
      (selectedProjector d k).PosSemidef ∧
      selectedProjector d k * selectedProjector d k = selectedProjector d k ∧
      (selectedProjector d k).rank = k := by
  exact RootRA09ThresholdTrace.actual_projector_structure d k hk
end

end RootRA09ThresholdTrace.Interface
