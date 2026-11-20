module

public import NLA.RA02.PaperRealPSD
public import NLA.RA02.PaperScaledInverse

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology
open Filter
namespace NLA.RA02.Paper

theorem complexify_one (n : ℕ) : complexify (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [complexify, Matrix.one_apply, h]

theorem complexify_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit A) :
    IsUnit (complexify A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit ((Complex.ofRealHom.mapMatrix A).det)
  rw [← Complex.ofRealHom.map_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).map Complex.ofRealHom

theorem complexify_inverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit A) :
    complexify A⁻¹ = (complexify A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← complexify_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), complexify_one]

theorem complexify_smul {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    complexify (a • A) = (a : ℂ) • complexify A := by
  ext i j
  simp [complexify, Matrix.smul_apply]

theorem complexify_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (complexify A).PosDef := by
  let h := hA.isHermitian
  let U := h.eigenvectorUnitary
  have hu : IsUnit (U : Matrix (Fin n) (Fin n) ℝ) :=
    (Unitary.toUnits U).isUnit
  have hspec : A = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal h.eigenvalues *
      (U : Matrix (Fin n) (Fin n) ℝ).transpose := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using h.spectral_theorem
  have he := congrArg complexify hspec
  rw [complexify_mul, complexify_mul, complexify_transpose, complexify_diagonal] at he
  rw [he]
  have hd : (Matrix.diagonal (fun i : Fin n => (h.eigenvalues i : ℂ))).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact Complex.pos_iff.mpr ⟨hA.eigenvalues_pos i, rfl⟩
  exact hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr (complexify_isUnit _ hu))

theorem continuous_complexify (n : ℕ) : Continuous (complexify (n:=n)) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => (A i j : ℂ))
  fun_prop

theorem continuous_complex_euclidean_operator {n : ℕ} :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜:=ℂ) A) := by
  let f := (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact f.continuous_of_finiteDimensional

theorem complex_lastProjection_norm (r : ℕ) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify (lastCoordinateProjection r))‖ = 1 := by
  have hd : complexify (lastCoordinateProjection r) =
      Matrix.diagonal (Pi.single (Fin.last r) (1 : ℂ)) := by
    rw [lastCoordinateProjection, complexify_diagonal]
    congr 1
    funext i
    by_cases hi : i = Fin.last r <;> simp [Pi.single_apply, hi]
  rw [hd]
  calc
    _ = ‖(Pi.single (Fin.last r) (1 : ℂ) : Fin (r+1) → ℂ)‖ :=
      Matrix.l2_opNorm_diagonal (Pi.single (Fin.last r) (1 : ℂ))
    _ = 1 := by
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro i
        by_cases hi : i = Fin.last r <;> simp [Pi.single_apply, hi]
      · have hh := norm_le_pi_norm (Pi.single (Fin.last r) (1 : ℂ) : Fin (r+1) → ℂ) (Fin.last r)
        simpa using hh

theorem complex_scaled_inverse_norm_limit (r : ℕ) :
    Tendsto (fun t : ℝ => ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify (scaledFamilyInverse r t))‖)
      (𝓝[>] 0) (𝓝 1) := by
  have hh := (continuous_complex_euclidean_operator (n:=r+1)).continuousAt.comp
    ((continuous_complexify (r+1)).continuousAt.comp (scaledFamilyInverse_continuousAt_zero r))
  have hn := hh.norm.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from inf_le_left)
  simpa only [Function.comp_apply, scaledFamilyInverse_zero, complex_lastProjection_norm] using hn

#print axioms complex_scaled_inverse_norm_limit
end NLA.RA02.Paper
