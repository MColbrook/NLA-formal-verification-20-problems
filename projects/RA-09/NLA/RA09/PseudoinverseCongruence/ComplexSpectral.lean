module

public import NLA.RA09.PseudoinverseCongruence.Definitions
public import NLA.RA09.ComplexHarmonicMatrix

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix MatrixOrder ComplexOrder
namespace RootRA09PseudoinverseCongruence
open NLA.RA09.ComplexPaper
open NLA.RA09.ComplexPaper (spectralCombination_mul)

theorem complex_combination_one {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    spectralCombination d (fun _ => 1) = 1 := by
  simpa [spectralCombination] using unitary_mul_star d.unitary

theorem complex_pseudoinverse_psd {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    (spectralPseudoinverse A).PosSemidef := by
  rw [spectralPseudoinverse,selected_cfc_eq d]
  exact spectralCombination_posSemidef d _ (fun i => inv_nonneg.mpr (d.nonnegative i))

theorem complex_inverseSqrt_spectral {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    complexInverseSqrt A = spectralCombination d (fun i => Real.sqrt ((d.eigenvalues i)⁻¹)) := by
  have hp : (spectralCombination d (fun i => Real.sqrt ((d.eigenvalues i)⁻¹))).PosSemidef :=
    spectralCombination_posSemidef d _ (fun _ => Real.sqrt_nonneg _)
  apply CFC.sqrt_unique _ hp.nonneg
  rw [spectralCombination_mul,spectralPseudoinverse,selected_cfc_eq d]
  congr 1
  funext i
  exact Real.mul_self_sqrt (inv_nonneg.mpr (d.nonnegative i))

theorem complex_support_spectral {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    complexSupportProjector A = spectralCombination d (fun i => if d.eigenvalues i = 0 then 0 else 1) := by
  have hP := selected_cfc_eq d (fun x : ℝ => x⁻¹)
  have hA : A = spectralCombination d d.eigenvalues := d.reconstruct
  change spectralPseudoinverse A = _ at hP
  unfold complexSupportProjector
  conv_lhs => lhs; rw [hA]
  rw [hP,spectralCombination_mul]
  congr 1
  funext i
  by_cases hi : d.eigenvalues i = 0 <;> simp [hi]

theorem actual_complex_square_root {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    IsMoorePenroseInverse A (spectralPseudoinverse A) ∧ (complexInverseSqrt A).PosSemidef ∧
      complexInverseSqrt A * complexInverseSqrt A = spectralPseudoinverse A ∧
      (complexInverseSqrt A).conjTranspose = complexInverseSqrt A ∧
      complexInverseSqrt A * A * complexInverseSqrt A = complexSupportProjector A := by
  have hp := complex_pseudoinverse_psd d
  have hw : (complexInverseSqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (spectralPseudoinverse A))
  have hsq : complexInverseSqrt A * complexInverseSqrt A = spectralPseudoinverse A :=
    CFC.sqrt_mul_sqrt_self _ hp.nonneg
  have hwt : (complexInverseSqrt A).conjTranspose = complexInverseSqrt A := by
    exact hw.isHermitian.eq
  refine ⟨spectralPseudoinverse_penrose d,hw,hsq,hwt,?_⟩
  have hA : A = spectralCombination d d.eigenvalues := d.reconstruct
  rw [complex_inverseSqrt_spectral d,complex_support_spectral d]
  conv_lhs => lhs; rhs; rw [hA]
  rw [spectralCombination_mul,spectralCombination_mul]
  congr 1
  funext i
  by_cases hi : d.eigenvalues i = 0
  · simp [hi]
  · simp only [if_neg hi]
    have hs := Real.mul_self_sqrt (inv_nonneg.mpr (d.nonnegative i))
    calc
      _ = d.eigenvalues i * (Real.sqrt ((d.eigenvalues i)⁻¹) * Real.sqrt ((d.eigenvalues i)⁻¹)) := by ring
      _ = 1 := by rw [hs,mul_inv_cancel₀ hi]

theorem actual_complex_support_projector {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    (complexSupportProjector A).PosSemidef ∧ complexSupportProjector A ≤ 1 ∧
      complexSupportProjector A * complexSupportProjector A = complexSupportProjector A ∧
      Set.range (fun x : Fin n → ℂ => complexSupportProjector A*ᵥx) =
        Set.range (fun x : Fin n → ℂ => A*ᵥx) := by
  have hp : (complexSupportProjector A).PosSemidef := by
    rw [complex_support_spectral d]
    apply spectralCombination_posSemidef
    intro i
    split_ifs <;> norm_num
  have hle : complexSupportProjector A ≤ 1 := by
    rw [complex_support_spectral d,← complex_combination_one d]
    apply spectralCombination_le
    intro i
    split_ifs <;> norm_num
  have hpa : complexSupportProjector A*A = A := (spectralPseudoinverse_penrose d).1
  have hi : complexSupportProjector A*complexSupportProjector A = complexSupportProjector A := by
    change (A*spectralPseudoinverse A)*(A*spectralPseudoinverse A)=A*spectralPseudoinverse A
    rw [← Matrix.mul_assoc]
    change (complexSupportProjector A*A)*spectralPseudoinverse A = A*spectralPseudoinverse A
    rw [hpa]
  refine ⟨hp,hle,hi,?_⟩
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨spectralPseudoinverse A*ᵥx,?_⟩
    change A*ᵥ(spectralPseudoinverse A*ᵥx) = (A*spectralPseudoinverse A)*ᵥx
    exact Matrix.mulVec_mulVec x A (spectralPseudoinverse A)
  · rintro ⟨x,rfl⟩
    refine ⟨A*ᵥx,?_⟩
    change complexSupportProjector A*ᵥ(A*ᵥx) = A*ᵥx
    rw [Matrix.mulVec_mulVec,hpa]

#print axioms actual_complex_square_root
#print axioms actual_complex_support_projector
end RootRA09PseudoinverseCongruence
