module

public import NLA.IV04.ConcreteOracleSearchProof.AutomaticPrecision
public import NLA.IV04.SharpActiveCramer.Attainment
public import NLA.IV04.SharpActiveCramer.Size

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
noncomputable section
open scoped Matrix
open IV04.Paper.Computational IV04.Paper.InequalityCertificate
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment
open Reference.IV04SharpActiveCramer
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem integer_tight_point_sharp_positive_common_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (x : Fin n → ℝ) (H : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (hkernel : ∀ d : Fin n → ℝ,
      (∀ i ∈ tightRows (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x,
        (Reference.IV04ConcreteOracleSearch.integerRealMatrix A *ᵥ d) i=0) → d=0) :
    ∃ p : Fin n → ℤ, ∃ d : ℕ, 0<d ∧ d≤Reference.IV04ConcreteOracleSearch.sharpCertificateBound n H ∧
      (∀ j, |p j|≤(Reference.IV04ConcreteOracleSearch.sharpCertificateBound n H : ℤ)) ∧
      ∀ j, x j=(p j : ℝ)/(d : ℝ) := by
  simp only [Reference.IV04ConcreteOracleSearchProof.integerRealMatrix_frozen,
    Reference.IV04ConcreteOracleSearchProof.integerRealVector_frozen] at *
  classical
  let AQ := integerRationalMatrix A
  let bQ := integerRationalVector b
  have hkQ : ∀ d : Fin n → ℝ,
      (∀ i ∈ tightRows (Reference.IV04AffinePolyhedronSteps.realMatrix AQ) (Reference.IV04AffinePolyhedronSteps.realVector bQ) x, (Reference.IV04AffinePolyhedronSteps.realMatrix AQ *ᵥ d) i=0) → d=0 := by
    simpa only [AQ,bQ,realMatrix_integerRationalMatrix,realVector_integerRationalVector] using hkernel
  let M := activeMatrix AQ bQ x
  have hgram : (Mᵀ*M).det ≠ 0 := (rational_tight_cramer_recovery AQ bQ x hkQ).1
  obtain ⟨f,hfinj,hfdet⟩ := exists_nonsingular_selected_rows M hgram
  have hli : LinearIndependent ℚ (M.submatrix f id).row :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hfdet))
  have hactive (i : Fin n) : f i ∈ tightRows (Reference.IV04AffinePolyhedronSteps.realMatrix AQ) (Reference.IV04AffinePolyhedronSteps.realVector bQ) x := by
    by_contra hi
    have hz : (M.submatrix f id).row i=0 := by
      funext j
      change activeMatrix AQ bQ x (f i) j=0
      simp [activeMatrix,hi]
    exact (hli.ne_zero i) hz
  let N := A.submatrix f id
  let v : Fin n → ℤ := fun i => b (f i)
  have hmapN : integerRationalMatrix N=M.submatrix f id := by
    ext i j
    change (A (f i) j : ℚ)=if f i ∈ tightRows (Reference.IV04AffinePolyhedronSteps.realMatrix AQ) (Reference.IV04AffinePolyhedronSteps.realVector bQ) x
      then (A (f i) j : ℚ) else 0
    rw [if_pos (hactive i)]
  have hNcast : (N.det : ℚ)=(integerRationalMatrix N).det := (Int.castRingHom ℚ).map_det N
  have hNdet : N.det ≠ 0 := by
    intro hz
    apply hfdet
    rw [← hmapN,← hNcast,hz]
    norm_num
  have hsys : Reference.IV04AffinePolyhedronSteps.integerRealMatrix N *ᵥ x=Reference.IV04AffinePolyhedronSteps.integerRealVector v := by
    funext i
    have hT := (mem_tightRows (Reference.IV04AffinePolyhedronSteps.realMatrix AQ) (Reference.IV04AffinePolyhedronSteps.realVector bQ) x (f i)).mp (hactive i)
    rw [show Reference.IV04AffinePolyhedronSteps.realMatrix AQ=Reference.IV04AffinePolyhedronSteps.integerRealMatrix A from realMatrix_integerRationalMatrix A,
      show Reference.IV04AffinePolyhedronSteps.realVector bQ=Reference.IV04AffinePolyhedronSteps.integerRealVector b from realVector_integerRationalVector b] at hT
    change (Reference.IV04AffinePolyhedronSteps.integerRealMatrix A *ᵥ x) (f i)=Reference.IV04AffinePolyhedronSteps.integerRealVector b (f i)
    exact hT
  have hNH : ∀ i j, |N i j| ≤ (H : ℤ) := fun i j => hA (f i) j
  have hvH : ∀ i, |v i| ≤ (H : ℤ) := fun i => hb (f i)
  obtain ⟨p,d,hd,hdQ,hpQ,hcoords⟩ := integer_square_system_sharp_certificate N v x H hNH hvH hNdet hsys
  exact normalize_common_denominator x p d (Reference.IV04ConcreteOracleSearch.sharpCertificateBound n H) hd hdQ hpQ hcoords

theorem actual_original_optimum_polynomial_certificate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) (j : Fin n)
    (hne : ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hline : lineFree (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)) (upper : ℝ)
    (hupper : ∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤upper) :
    ∃ p : Fin n → ℤ, ∃ d : ℕ, 0<d ∧
      feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) (fun k => (p k : ℝ)/(d : ℝ)) ∧
      (∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤(p j : ℝ)/(d : ℝ)) ∧
      (Reference.IV04ConcreteOracleSearch.inequalityIntegerCertificateCode (Reference.IV04ConcreteOracleSearch.integerVectorList p) d).length≤
        Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length := by
  simp only [Reference.IV04ConcreteOracleSearchProof.integerRealMatrix_frozen,
    Reference.IV04ConcreteOracleSearchProof.integerRealVector_frozen] at *
  let N := (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length
  obtain ⟨hA,hb⟩ := matrix_coefficients_le_instance_power A b
  obtain ⟨q,hq,hmax,_⟩ := integer_original_extreme_objective_attained_sharp_size
    A b (2^N) hA hb (LinearMap.proj j) upper hne hline hupper
  have hk := extreme_point_tight_kernel_trivial _ _ _ hq
  obtain ⟨p,d,hd,hdQ,hpQ,hcoords⟩ := Reference.IV04ConcreteOracleSearchProof.integer_tight_point_sharp_positive_common_certificate
    A b (Reference.IV04AffinePolyhedronSteps.realVector q) (2^N) hA hb hk
  have heq : Reference.IV04AffinePolyhedronSteps.realVector q=(fun k => (p k : ℝ)/(d : ℝ)) := funext hcoords
  have hfeas : feasible (Reference.IV04AffinePolyhedronSteps.integerRealMatrix A) (Reference.IV04AffinePolyhedronSteps.integerRealVector b)
      (fun k => (p k : ℝ)/(d : ℝ)) := heq ▸ hq.1
  have hmaximum : ∀ x, feasible (Reference.IV04AffinePolyhedronSteps.integerRealMatrix A) (Reference.IV04AffinePolyhedronSteps.integerRealVector b) x → x j≤(p j : ℝ)/(d : ℝ) := by
    intro x hx
    simpa only [LinearMap.proj_apply,heq] using hmax x hx
  obtain ⟨_,hnN⟩ := matrix_dimensions_le_instance_length A b hm
  change n≤N at hnN
  have hK : n*n+n*N≤2*N*N := by
    have hsq := Nat.mul_le_mul hnN hnN
    have hprod := Nat.mul_le_mul_right N hnN
    nlinarith
  have hQ : Reference.IV04ConcreteOracleSearch.sharpCertificateBound n (2^N)≤2^(2*N*N) :=
    (sharpCertificateBound_le_two_pow n (2^N) N (le_refl _)).trans
      (Nat.pow_le_pow_right (by omega) hK)
  have hdP := hdQ.trans hQ
  have hpP : ∀ z ∈ Reference.IV04ConcreteOracleSearch.integerVectorList p, |z|≤((2^(2*N*N) : ℕ) : ℤ) := by
    intro z hz
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hz
    exact (hpQ k).trans (by exact_mod_cast hQ)
  have hlen := integer_certificate_length_bound (Reference.IV04ConcreteOracleSearch.integerVectorList p) d (2*N*N) hpP hdP
  simp only [Reference.IV04ConcreteOracleSearch.integerVectorList,List.length_ofFn] at hlen
  have hpoly : (4*n+1)*(2*N*N+3)≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial N := by
    unfold Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial
    apply Nat.mul_le_mul (by omega)
    nlinarith
  exact ⟨p,d,hd,hfeas,hmaximum,hlen.trans hpoly⟩

theorem actual_bounded_coordinate_recovery {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) (j : Fin n)
    (hne : ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hline : lineFree (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)) (upper : ℝ)
    (hupper : ∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤upper) :
    let bound := Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length
    ∃ maximum : ℚ, Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)=some maximum ∧
      (∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x ∧ x j=(maximum : ℝ)) ∧
      (∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤(maximum : ℝ)) ∧
      (Reference.IV04ConcreteOracleSearch.executeCounting (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)).2≤4*bound+2 := by
  simp only [Reference.IV04ConcreteOracleSearchProof.integerRealMatrix_frozen,
    Reference.IV04ConcreteOracleSearchProof.integerRealVector_frozen] at *
  obtain ⟨p,d,hd,hx,hmax,hlen⟩ := Reference.IV04ConcreteOracleSearchProof.actual_original_optimum_polynomial_certificate A b hm j hne hline upper hupper
  refine ⟨(p j : ℚ)/(d : ℚ),Reference.IV04ConcreteOracleSearchProof.boundedCoordinateRecovery_actual_output_exact A b j p d hd hx hmax _ hlen,
    ⟨fun k => (p k : ℝ)/(d : ℝ),hx,by simp⟩,?_,Reference.IV04ConcreteOracleSearchProof.boundedCoordinateRecovery_actual_query_count _ _ _ _⟩
  simpa [Reference.IV04ConcreteOracleSearchProof.integerRealMatrix_frozen,
    Reference.IV04ConcreteOracleSearchProof.integerRealVector_frozen] using hmax

#print axioms integer_tight_point_sharp_positive_common_certificate

#print axioms actual_original_optimum_polynomial_certificate

#print axioms actual_bounded_coordinate_recovery
end
end Reference.IV04ConcreteOracleSearchProof
