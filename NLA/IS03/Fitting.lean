module

public import NLA.IS03.Spectral
public import NLA.IS03.Newton
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

/-!
Remove an arbitrary nilpotent zero-eigenvalue block by the Fitting decomposition.
This supplies the matrix bridge needed for the manuscript's zero-padding claim;
the proposed realizing matrix is not assumed diagonalizable.
-/

noncomputable section
open Polynomial Module Module.Free LinearMap
open scoped Classical
namespace NLA.IS03

theorem exists_unpadded_matrix {n : ℕ} (B : RealMatrix n) (r : ℕ)
    (hB : B.charpoly = X ^ r * derivativePolynomial) :
    ∃ C : RealMatrix 6, C.charpoly = derivativePolynomial ∧
      ∀ k : ℕ, k ≠ 0 → Matrix.trace (B ^ k) = Matrix.trace (C ^ k) := by
  let φ : Module.End ℝ (Fin n → ℝ) := B.toLin'
  have hφ : φ.charpoly = X ^ r * derivativePolynomial := by
    simpa only [φ, Matrix.charpoly_toLin'] using hB
  set V := φ.maxGenEigenspace 0
  have hV : V = ⨆ (j : ℕ), ker (φ ^ j) := by
    simp [V, ← Module.End.iSup_genEigenspace_eq, Module.End.genEigenspace_nat]
  let W := ⨅ (j : ℕ), LinearMap.range (φ ^ j)
  have hVW : IsCompl V W := by
    rw [hV]
    exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow φ
  have hφV : ∀ x ∈ V, φ x ∈ V := by
    simp only [V, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero,
      forall_exists_index]
    intro x j hx
    use j
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]
  have hφW : ∀ x ∈ W, φ x ∈ W := by
    simp only [W, Submodule.mem_iInf, mem_range]
    intro x H j
    obtain ⟨y, rfl⟩ := H j
    use φ y
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
  let F := φ.restrict hφV
  let G := φ.restrict hφW
  let ψ := F.prodMap G
  let e := Submodule.prodEquivOfIsCompl V W hVW
  let b := (chooseBasis ℝ V).prod (chooseBasis ℝ W)
  have hψ : ψ = e.symm.conj φ := by
    apply b.ext
    simp only [Basis.prod_apply, coe_inl, coe_inr, prodMap_apply, LinearEquiv.conj_apply,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl, coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, coprod_apply, Submodule.coe_subtype, map_add, Sum.forall, Sum.elim_inl,
      map_zero, ZeroMemClass.coe_zero, add_zero, LinearEquiv.eq_symm_apply, and_self,
      Submodule.coe_prodEquivOfIsCompl', coe_restrict_apply, implies_true, Sum.elim_inr, zero_add,
      e, V, W, ψ, F, G, b]
  have hF : IsNilpotent F := by
    apply ((charpoly_nilpotent_tfae F).out 3 1).mp
    simp only [Subtype.forall, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V, F]
    rintro x ⟨j, hx⟩
    use j
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    refine .trans ?_ hx
    generalize_proofs h'
    clear hx
    induction j <;> simp [pow_succ', *]
  have hq0 : constantCoeff derivativePolynomial ≠ 0 := by
    norm_num [derivativePolynomial]
  have hdimV : finrank ℝ V = r := by
    rw [LinearMap.finrank_maxGenEigenspace_zero_eq, hφ,
      natTrailingDegree_mul (pow_ne_zero _ X_ne_zero) derivativePolynomial_monic.ne_zero,
      natTrailingDegree_X_pow, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hq0,
      add_zero]
  have hFchar : F.charpoly = X ^ r := by
    rw [hF.charpoly_eq_X_pow_finrank, hdimV]
  have hGchar : G.charpoly = derivativePolynomial := by
    apply mul_left_cancel₀ (pow_ne_zero r (X_ne_zero : (X : ℝ[X]) ≠ 0))
    calc
      X ^ r * G.charpoly = ψ.charpoly := by rw [charpoly_prodMap, hFchar]
      _ = φ.charpoly := by rw [hψ, LinearEquiv.charpoly_conj]
      _ = X ^ r * derivativePolynomial := hφ
  have hdimW : finrank ℝ W = 6 := by
    rw [← G.charpoly_natDegree, hGchar, derivativePolynomial_degree]
  let c := (Module.finBasis ℝ W).reindex (finCongr hdimW)
  let C : RealMatrix 6 := LinearMap.toMatrix c c G
  refine ⟨C, ?_, ?_⟩
  · exact (LinearMap.charpoly_toMatrix G c).trans hGchar
  · intro k hk
    have hp : ψ ^ k = (F ^ k).prodMap (G ^ k) := by
      simpa only [ψ, prodMapRingHom_apply, Prod.pow_mk] using
        (map_pow (LinearMap.prodMapRingHom (R := ℝ) (M := V) (M₂ := W)) (F, G) k).symm
    have hnil : LinearMap.trace ℝ V (F ^ k) = 0 :=
      (LinearMap.isNilpotent_trace_of_isNilpotent (hF.pow_of_pos hk)).eq_zero
    calc
      Matrix.trace (B ^ k) = LinearMap.trace ℝ (Fin n → ℝ) (φ ^ k) := by
        rw [← Matrix.toLin'_pow, Matrix.trace_toLin'_eq]
      _ = LinearMap.trace ℝ (V × W) (ψ ^ k) := by
        have hconj : e.symm.conj (φ ^ k) = (e.symm.conj φ) ^ k :=
          map_pow (e.symm.conjAlgEquiv ℝ) φ k
        rw [hψ, ← hconj, LinearMap.trace_conj']
      _ = LinearMap.trace ℝ W (G ^ k) := by rw [hp, trace_prodMap', hnil, zero_add]
      _ = Matrix.trace (C ^ k) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ c]
        congr 1
        exact map_pow (LinearMap.toMatrixAlgEquiv c) G k

theorem zero_padding_matrix_seventh_trace {n : ℕ} (B : RealMatrix n) (r : ℕ)
    (hB : B.charpoly = X ^ r * derivativePolynomial) :
    Matrix.trace (B ^ 7) = -8593 / 823543 := by
  obtain ⟨C, hC, htrace⟩ := exists_unpadded_matrix B r hB
  rw [htrace 7 (by decide)]
  apply Complex.ofReal_injective
  obtain ⟨hprod, hpowers⟩ := root_product_and_trace C hC
  have h := power_sums_of_derivative_product (fun z : ComplexRoots => (z : ℂ))
    complexRoots_card hprod (6 : Fin 7)
  exact (hpowers 7).trans h

theorem zero_padding_nonrealizability {n : ℕ} (B : RealMatrix n)
    (hB : EntrywiseNonnegative B) (r : ℕ) :
    B.charpoly ≠ X ^ r * derivativePolynomial := by
  intro heq
  have hnonneg := (nonnegative_power_trace_proved B hB 7).2
  rw [zero_padding_matrix_seventh_trace B r heq] at hnonneg
  norm_num at hnonneg

#print axioms exists_unpadded_matrix
#print axioms zero_padding_matrix_seventh_trace
#print axioms zero_padding_nonrealizability

end NLA.IS03
