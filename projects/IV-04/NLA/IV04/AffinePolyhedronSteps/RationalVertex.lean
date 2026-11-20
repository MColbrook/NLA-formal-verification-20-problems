module

/- Genuine rational recovery from the actual full tight system, via its actual Gram matrix. -/
public import NLA.IV04.AffinePolyhedronSteps.SignedOrthant
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 def realMatrix {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ ℝ :=
  A.map (Rat.castHom ℝ)

 def realVector {ι : Type*} (b : ι → ℚ) : ι → ℝ := fun i => b i

 theorem realMatrix_transpose {ι κ : Type*} (A : Matrix ι κ ℚ) :
    realMatrix Aᵀ = (realMatrix A)ᵀ := rfl

 theorem realMatrix_mul {ι κ ν : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) (B : Matrix κ ν ℚ) :
    realMatrix (A*B) = realMatrix A*realMatrix B := by
  exact Matrix.map_mul

 theorem realVector_mulVec {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) (b : κ → ℚ) :
    realVector (A *ᵥ b)=realMatrix A *ᵥ realVector b := by
  funext i
  exact (Rat.castHom ℝ).map_mulVec A b i

 def activeMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (x : Fin n → ℝ) : Matrix ι (Fin n) ℚ := by
  classical
  exact fun i j => if i ∈ tightRows (realMatrix A) (realVector b) x then A i j else 0

 def activeBounds {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (x : Fin n → ℝ) : ι → ℚ := by
  classical
  exact fun i => if i ∈ tightRows (realMatrix A) (realVector b) x then b i else 0

 theorem activeMatrix_real_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (x d : Fin n → ℝ) (i : ι) :
    (realMatrix (activeMatrix A b x) *ᵥ d) i =
      if i ∈ tightRows (realMatrix A) (realVector b) x then (realMatrix A *ᵥ d) i else 0 := by
  classical
  by_cases hi : i ∈ tightRows (realMatrix A) (realVector b) x
  · rw [if_pos hi]
    change (∑ j, ((if i ∈ tightRows (realMatrix A) (realVector b) x then A i j else 0 : ℚ) : ℝ)*d j) = (realMatrix A *ᵥ d) i
    simp only [if_pos hi]
    rfl
  · rw [if_neg hi]
    change (∑ j, ((if i ∈ tightRows (realMatrix A) (realVector b) x then A i j else 0 : ℚ) : ℝ)*d j) = 0
    simp only [if_neg hi,Rat.cast_zero,zero_mul,Finset.sum_const_zero]
 theorem activeMatrix_real_system {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (x : Fin n → ℝ) :
    realMatrix (activeMatrix A b x) *ᵥ x = realVector (activeBounds A b x) := by
  classical
  funext i
  rw [activeMatrix_real_mulVec]
  by_cases hi : i ∈ tightRows (realMatrix A) (realVector b) x
  · simp only [if_pos hi]
    simpa [activeBounds,realVector,hi] using
      (mem_tightRows (realMatrix A) (realVector b) x i).mp hi
  · simp [activeBounds,realVector,hi]

 def cramerCandidate {n : ℕ} (G : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) :
    Fin n → ℚ := fun j => G.cramer c j/G.det

 theorem cramerCandidate_solution {n : ℕ} (G : Matrix (Fin n) (Fin n) ℚ)
    (c : Fin n → ℚ) (hdet : G.det ≠ 0) : G *ᵥ cramerCandidate G c=c := by
  have hc : cramerCandidate G c = G.det⁻¹ • G.cramer c := by
    funext j
    simp [cramerCandidate,div_eq_mul_inv,mul_comm]
  rw [hc,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hdet,one_smul]

 theorem cramerCandidate_coordinate {n : ℕ} (G : Matrix (Fin n) (Fin n) ℚ)
    (c : Fin n → ℚ) (j : Fin n) :
    cramerCandidate G c j=(G.updateCol j c).det/G.det := by
  simp only [cramerCandidate,Matrix.cramer_apply]

 theorem rational_tight_cramer_recovery {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (x : Fin n → ℝ)
    (hkernel : ∀ d : Fin n → ℝ,
      (∀ i ∈ tightRows (realMatrix A) (realVector b) x, (realMatrix A *ᵥ d) i=0) → d=0) :
    let M := activeMatrix A b x
    let G := Mᵀ*M
    let c := Mᵀ *ᵥ activeBounds A b x
    G.det ≠ 0 ∧ realVector (cramerCandidate G c)=x := by
  classical
  let M := activeMatrix A b x
  let G := Mᵀ*M
  let c := Mᵀ *ᵥ activeBounds A b x
  change G.det ≠ 0 ∧ realVector (cramerCandidate G c)=x
  have hMker : LinearMap.ker (realMatrix M).mulVecLin=⊥ := by
    apply (Matrix.ker_mulVecLin_eq_bot_iff).mpr
    intro d hd
    apply hkernel d
    intro i hi
    have he := congrFun hd i
    change (realMatrix (activeMatrix A b x) *ᵥ d) i=0 at he
    rw [activeMatrix_real_mulVec,if_pos hi] at he
    exact he
  have hGker : LinearMap.ker ((realMatrix M)ᵀ*realMatrix M).mulVecLin=⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self,hMker]
  have hGinj : Function.Injective ((realMatrix M)ᵀ*realMatrix M).mulVec :=
    LinearMap.ker_eq_bot.mp hGker
  have hGunit : IsUnit ((realMatrix M)ᵀ*realMatrix M) :=
    Matrix.mulVec_injective_iff_isUnit.mp hGinj
  have hGdetReal : ((realMatrix M)ᵀ*realMatrix M).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hGunit)
  have hmapG : realMatrix G=(realMatrix M)ᵀ*realMatrix M := by
    dsimp [G]
    rw [realMatrix_mul,realMatrix_transpose]
  have hdet : G.det ≠ 0 := by
    intro hz
    apply hGdetReal
    rw [← hmapG]
    have hcast : (G.det : ℝ) = (realMatrix G).det := (Rat.castHom ℝ).map_det G
    rw [← hcast,hz]
    simp
  have hsQ := cramerCandidate_solution G c hdet
  have hsR := congrArg realVector hsQ
  rw [realVector_mulVec] at hsR
  have hxR : realMatrix G *ᵥ x=realVector c := by
    calc
      realMatrix G *ᵥ x = (realMatrix M)ᵀ *ᵥ (realMatrix M *ᵥ x) := by
        rw [hmapG,Matrix.mulVec_mulVec]
      _ = (realMatrix M)ᵀ *ᵥ realVector (activeBounds A b x) := by
        rw [activeMatrix_real_system]
      _ = realVector c := by
        dsimp [c]
        rw [realVector_mulVec,realMatrix_transpose]
  refine ⟨hdet,?_⟩
  apply hGinj
  rw [← hmapG]
  exact hsR.trans hxR.symm

 theorem exists_rational_extreme_point_of_lineFree {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ)
    (hne : ∃ x, feasible (realMatrix A) (realVector b) x)
    (hline : lineFree (realMatrix A) (realVector b)) :
    ∃ q : Fin n → ℚ, realVector q ∈ (feasibleSet (realMatrix A) (realVector b)).extremePoints ℝ := by
  obtain ⟨x,hx,hkernel⟩ := exists_extreme_point_of_lineFree (realMatrix A) (realVector b) hne hline
  have hrec := rational_tight_cramer_recovery A b x hkernel
  exact ⟨cramerCandidate _ _,hrec.2.symm ▸ hx⟩

#print axioms realVector_mulVec
#print axioms activeMatrix_real_mulVec
#print axioms activeMatrix_real_system
#print axioms cramerCandidate_solution
#print axioms cramerCandidate_coordinate
#print axioms rational_tight_cramer_recovery
#print axioms exists_rational_extreme_point_of_lineFree
end
end Reference.IV04AffinePolyhedronSteps
