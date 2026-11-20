module

/- Sharp n! H^n bounds from actual n independent original active rows. -/
public import NLA.IV04.SharpActiveCramer.SquareCertificate

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04SharpActiveCramer
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem integer_tight_point_sharp_reduced_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (x : Fin n → ℝ) (H : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (hkernel : ∀ d : Fin n → ℝ,
      (∀ i ∈ tightRows (integerRealMatrix A) (integerRealVector b) x,
        (integerRealMatrix A *ᵥ d) i=0) → d=0) :
    ∃ q : Fin n → ℚ, realVector q=x ∧
      ∀ j, (q j).den ≤ sharpCertificateBound n H ∧
        (q j).num.natAbs ≤ sharpCertificateBound n H := by
  classical
  let AQ := integerRationalMatrix A
  let bQ := integerRationalVector b
  have hkQ : ∀ d : Fin n → ℝ,
      (∀ i ∈ tightRows (realMatrix AQ) (realVector bQ) x, (realMatrix AQ *ᵥ d) i=0) → d=0 := by
    simpa only [AQ,bQ,realMatrix_integerRationalMatrix,realVector_integerRationalVector] using hkernel
  let M := activeMatrix AQ bQ x
  have hgram : (Mᵀ*M).det ≠ 0 := (rational_tight_cramer_recovery AQ bQ x hkQ).1
  obtain ⟨f,hfinj,hfdet⟩ := exists_nonsingular_selected_rows M hgram
  have hli : LinearIndependent ℚ (M.submatrix f id).row :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hfdet))
  have hactive (i : Fin n) : f i ∈ tightRows (realMatrix AQ) (realVector bQ) x := by
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
    change (A (f i) j : ℚ)=if f i ∈ tightRows (realMatrix AQ) (realVector bQ) x
      then (A (f i) j : ℚ) else 0
    rw [if_pos (hactive i)]
  have hNcast : (N.det : ℚ)=(integerRationalMatrix N).det := (Int.castRingHom ℚ).map_det N
  have hNdet : N.det ≠ 0 := by
    intro hz
    apply hfdet
    rw [← hmapN,← hNcast,hz]
    norm_num
  have hsys : integerRealMatrix N *ᵥ x=integerRealVector v := by
    funext i
    have hT := (mem_tightRows (realMatrix AQ) (realVector bQ) x (f i)).mp (hactive i)
    rw [show realMatrix AQ=integerRealMatrix A from realMatrix_integerRationalMatrix A,
      show realVector bQ=integerRealVector b from realVector_integerRationalVector b] at hT
    change (integerRealMatrix A *ᵥ x) (f i)=integerRealVector b (f i)
    exact hT
  have hNH : ∀ i j, |N i j| ≤ (H : ℤ) := fun i j => hA (f i) j
  have hvH : ∀ i, |v i| ≤ (H : ℤ) := fun i => hb (f i)
  obtain ⟨p,d,hd,hdQ,hpQ,hcoords⟩ := integer_square_system_sharp_certificate N v x H hNH hvH hNdet hsys
  let q : Fin n → ℚ := fun j => (p j : ℚ)/(d : ℚ)
  have hqx : realVector q=x := by
    funext j
    simpa [realVector,q] using (hcoords j).symm
  refine ⟨q,hqx,?_⟩
  intro j
  exact ⟨rational_den_le_of_integer_fraction (q j) (p j) d _ hd rfl hdQ,
    rational_num_natAbs_le_of_integer_fraction (q j) (p j) d _ hd rfl (hpQ j)⟩

#print axioms integer_tight_point_sharp_reduced_certificate
end
end Reference.IV04SharpActiveCramer
