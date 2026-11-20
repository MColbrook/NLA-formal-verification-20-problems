module

/- Actual integer Gram/Cramer certificates of a real solution of a full-column-rank system. -/
public import NLA.IV04.AffinePolyhedronSteps.GramBounds

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

def integerRealMatrix {ι κ : Type*} (M : Matrix ι κ ℤ) : Matrix ι κ ℝ :=
  M.map (Int.castRingHom ℝ)
def integerRealVector {ι : Type*} (b : ι → ℤ) : ι → ℝ := fun i => b i

theorem integer_full_system_certificate {ι : Type*} [Fintype ι] {n : ℕ}
    (M : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (x : Fin n → ℝ) (H : ℕ)
    (hx : integerRealMatrix M *ᵥ x=integerRealVector b)
    (hk : ∀ d : Fin n → ℝ, integerRealMatrix M *ᵥ d=0 → d=0)
    (hM : ∀ i j, |M i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ)) :
    ∃ p : Fin n → ℤ, ∃ d : ℤ,
      d ≠ 0 ∧ |d| ≤ (gramCertificateBound (Fintype.card ι) n H : ℤ) ∧
      (∀ j, |p j| ≤ (gramCertificateBound (Fintype.card ι) n H : ℤ)) ∧
      ∀ j, x j=(p j : ℝ)/(d : ℝ) := by
  classical
  let G := Mᵀ*M
  let c := Mᵀ *ᵥ b
  have hmapG : integerRealMatrix G=(integerRealMatrix M)ᵀ*integerRealMatrix M := by
    change (Mᵀ*M).map (Int.castRingHom ℝ)=
      (Mᵀ.map (Int.castRingHom ℝ))*(M.map (Int.castRingHom ℝ))
    exact Matrix.map_mul
  have hmapc : integerRealVector c=(integerRealMatrix M)ᵀ *ᵥ integerRealVector b := by
    funext i
    exact (Int.castRingHom ℝ).map_mulVec Mᵀ b i
  have hker : LinearMap.ker (integerRealMatrix M).mulVecLin=⊥ :=
    Matrix.ker_mulVecLin_eq_bot_iff.mpr hk
  have hGker : LinearMap.ker ((integerRealMatrix M)ᵀ*integerRealMatrix M).mulVecLin=⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self,hker]
  have hGinj : Function.Injective ((integerRealMatrix M)ᵀ*integerRealMatrix M).mulVec :=
    LinearMap.ker_eq_bot.mp hGker
  have hGdet : ((integerRealMatrix M)ᵀ*integerRealMatrix M).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hGinj))
  have hcast : (G.det : ℝ)=(integerRealMatrix G).det := (Int.castRingHom ℝ).map_det G
  have hdR : (G.det : ℝ) ≠ 0 := by
    rw [hcast,hmapG]
    exact hGdet
  have hd : G.det ≠ 0 := by exact_mod_cast hdR
  have hxG : integerRealMatrix G *ᵥ x=integerRealVector c := by
    rw [hmapG,← Matrix.mulVec_mulVec,hx,← hmapc]
  let y : Fin n → ℝ := fun j =>
    (integerRealMatrix G).cramer (integerRealVector c) j/(integerRealMatrix G).det
  have hyG : integerRealMatrix G *ᵥ y=integerRealVector c := by
    have hy : y=(integerRealMatrix G).det⁻¹ •
        (integerRealMatrix G).cramer (integerRealVector c) := by
      funext j
      simp [y,div_eq_mul_inv,mul_comm]
    rw [hy,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul]
    rw [inv_mul_cancel₀ (hcast ▸ hdR),one_smul]
  have hxy : x=y := by
    apply hGinj
    rw [← hmapG,hxG,hyG]
  have hbounds := integer_gram_cramer_bounds M b H hM hb
  refine ⟨fun j => (G.updateCol j c).det,G.det,hd,hbounds.1,hbounds.2,?_⟩
  intro j
  rw [hxy]
  dsimp [y]
  rw [Matrix.cramer_apply,← hcast]
  have hnum : ((G.updateCol j c).det : ℝ)=
      ((integerRealMatrix G).updateCol j (integerRealVector c)).det := by
    calc
      _ = (integerRealMatrix (G.updateCol j c)).det := (Int.castRingHom ℝ).map_det _
      _ = _ := by
        congr 1
        exact Matrix.map_updateCol (Int.castRingHom ℝ)
  rw [← hnum]

#print axioms integer_full_system_certificate
end
end Reference.IV04AffinePolyhedronSteps
