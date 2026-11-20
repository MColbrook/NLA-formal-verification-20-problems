module

public import NLA.RA09.Paper.Conclusions
public import NLA.RA09.Paper.Degenerate
public import NLA.RA09.Paper.OrderedSharpness
public import NLA.RA09.Paper.Sharpness
public import NLA.RA09.Paper.Powers
public import NLA.RA09.Paper.OperatorPowers
public import NLA.RA09.Paper.ScalarCertificate
public import NLA.RA09.Paper.HarmonicMatrix
public import NLA.RA09.UnorderedScalar

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix
namespace NLA.RA09

theorem paper_ordered_matrix_excess {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) - functionTail dA f k ≤
      (transferScale f (dA.eigenvalues ⟨k,hk⟩))^2 *
        (frobeniusSquared (A-B) - spectralTail dA k) := by
  apply Paper.ordered_matrix_excess <;> assumption

theorem paper_unordered_matrix_excess {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) - functionTail dA f k ≤
      2*(transferScale f (dA.eigenvalues ⟨k,hk⟩))^2 *
        (frobeniusSquared (A-B) - spectralTail dA k) := by
  apply Paper.unordered_matrix_excess <;> assumption

theorem paper_ordered_matrix_squared_relative {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (η : ℝ) (hη : 0 ≤ η) (hA : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+η)*functionTail dA f k := by
  apply Paper.ordered_matrix_squared_relative <;> assumption

theorem paper_unordered_matrix_squared_relative {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (η : ℝ) (hη : 0 ≤ η) (hA : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+2*η)*functionTail dA f k := by
  apply Paper.unordered_matrix_squared_relative <;> assumption

theorem paper_ordered_matrix_norm_relative {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hA : frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt (spectralTail dA k)) :
    frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+ε)*Real.sqrt (functionTail dA f k) := by
  apply Paper.ordered_matrix_norm_relative <;> assumption

theorem paper_unordered_matrix_norm_relative {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hA : frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt (spectralTail dA k)) :
    frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+2*ε)*Real.sqrt (functionTail dA f k) := by
  apply Paper.unordered_matrix_norm_relative <;> assumption

theorem paper_spectral_tail_zero_of_cutoff_zero {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (hk : k < n)
    (hzero : d.eigenvalues ⟨k,hk⟩ = 0) : spectralTail d k = 0 := by
  apply Paper.spectral_tail_zero_of_cutoff_zero <;> assumption

theorem paper_spectral_tail_full {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) : spectralTail d n = 0 := by
  apply Paper.spectral_tail_full <;> assumption

theorem paper_zero_tail_residual_exact {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (k : ℕ) (hk : k ≤ n) (hB : B.rank ≤ k)
    (hzero : spectralTail dA k = 0) (η : ℝ)
    (herror : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    A = B ∧ frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) =
      functionTail dA f k := by
  apply Paper.zero_tail_residual_exact <;> assumption

theorem paper_identity_admissible : PaperAdmissibleFunction (fun x : ℝ => x) := by
  apply Paper.identity_admissible <;> assumption

theorem paper_ordered_sharpness (γ : ℝ) (hγ : γ < 1) :
    ∃ (A B : RealMatrix 3) (dA : OrderedSpectralData A) (dB : OrderedSpectralData B),
      B ≤ A ∧ B.rank ≤ 1 ∧ dA.eigenvalues ⟨1, by decide⟩ = 1 ∧
      frobeniusSquared (A-B) - spectralTail dA 1 = 1 ∧
      γ * (frobeniusSquared (A-B) - spectralTail dA 1) <
        frobeniusSquared (functionalCalculus (fun x : ℝ => x) A -
          functionTruncation dB (fun x : ℝ => x) 1) - functionTail dA (fun x : ℝ => x) 1 := by
  apply Paper.ordered_sharpness <;> assumption

theorem paper_unordered_sharpness (γ : ℝ) (hγ : γ < 2) : UnorderedSharpnessWitness γ := by
  apply Paper.unordered_sharpness <;> assumption

theorem paper_power_admissible {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    PaperAdmissibleFunction (fun x : ℝ => x ^ p) := by
  apply Paper.power_admissible <;> assumption

theorem paper_power_operator_monotone {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : X ≤ Y) :
    cfc (fun x : ℝ => x ^ p) X ≤ cfc (fun x : ℝ => x ^ p) Y := by
  apply Paper.power_operator_monotone <;> assumption

theorem paper_ordered_scalar_certificate (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ a b : ℝ) (hτ : 0 < τ) (ha : 0 < a) (hb : 0 < b) :
    f b * max (f b - transferScale f τ * b) 0 * (1-b/a) ≤
      scalarAuxiliary f τ a + 2*f b*f a - 2*(transferScale f τ)^2*b*a -
        (f b)^2 + (transferScale f τ)^2*b^2 := by
  apply Paper.ordered_scalar_certificate <;> assumption

theorem paper_harmonic_matrix_full {n : ℕ} (A : RealMatrix n)
    (v : Fin n → ℝ) (b : ℝ) (hv : ∑ i, v i^2 = 1) (hb : 0 < b)
    (horder : b • outerSquare v ≤ A) :
    IsMoorePenroseInverse A (spectralPseudoinverse A) ∧
      v ∈ Set.range (fun x : Fin n → ℝ => A *ᵥ x) ∧
      b * (v ⬝ᵥ (spectralPseudoinverse A *ᵥ v)) ≤ 1 := by
  apply Paper.harmonic_matrix_full <;> assumption

theorem paper_unordered_scalar (g : ℝ → ℝ)
    (hg : PaperAdmissibleFunction g) (hg1 : g 1 = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    g b^2 - 2*g b*g a - 2*b^2 + 4*a*b ≤ max (2*a^2-g a^2) 1 := by
  apply unordered_scalar_certificate_proved <;> assumption

#print axioms NLA.RA09.paper_ordered_matrix_excess
#print axioms NLA.RA09.paper_unordered_matrix_excess
#print axioms NLA.RA09.paper_ordered_matrix_squared_relative
#print axioms NLA.RA09.paper_unordered_matrix_squared_relative
#print axioms NLA.RA09.paper_ordered_matrix_norm_relative
#print axioms NLA.RA09.paper_unordered_matrix_norm_relative
#print axioms NLA.RA09.paper_spectral_tail_zero_of_cutoff_zero
#print axioms NLA.RA09.paper_spectral_tail_full
#print axioms NLA.RA09.paper_zero_tail_residual_exact
#print axioms NLA.RA09.paper_identity_admissible
#print axioms NLA.RA09.paper_ordered_sharpness
#print axioms NLA.RA09.paper_unordered_sharpness
#print axioms NLA.RA09.paper_power_admissible
#print axioms NLA.RA09.paper_power_operator_monotone
#print axioms NLA.RA09.paper_ordered_scalar_certificate
#print axioms NLA.RA09.paper_harmonic_matrix_full
#print axioms NLA.RA09.paper_unordered_scalar
end NLA.RA09
