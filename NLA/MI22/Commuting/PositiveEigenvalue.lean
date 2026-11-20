module

public import NLA.MI22.Commuting.EigenAction

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Unitary
namespace NLA.MI22.Commuting

theorem eigenvalue_positive {n : ℕ} (A : Mat n) (hA : A.PosDef)
    (v : Fin n → ℂ) (a : ℝ) (hv : A *ᵥ v = (a : ℂ) • v) (hv0 : v ≠ 0) : 0 < a := by
  let U := hA.isHermitian.eigenvectorUnitary
  let w := (star U : Mat n) *ᵥ v
  have hU : (star U : Mat n) * (U : Mat n) = 1 := Unitary.coe_star_mul_self U
  have hUs : (U : Mat n) * (star U : Mat n) = 1 := Unitary.coe_mul_star_self U
  have hd : A = (U : Mat n) * diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) *
      (star U : Mat n) := by
    simpa only [Real.rpow_one, U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      (spectralPower_one A hA).symm.trans (spectral_power_semantics_proved A hA 1)
  have hleft : (star U : Mat n) * A =
      diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) * (star U : Mat n) := by
    calc
      (star U : Mat n) * A = (star U : Mat n) * ((U : Mat n) * diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) * (star U : Mat n)) := congrArg (fun M => (star U : Mat n) * M) hd
      _ = _ := by simp only [← mul_assoc, hU, one_mul]
  have hw : diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) *ᵥ w = (a : ℂ) • w := by
    dsimp only [w]
    rw [mulVec_mulVec, ← hleft, ← mulVec_mulVec, hv, mulVec_smul]
  have hw0 : w ≠ 0 := by
    intro hz
    apply hv0
    have he : (U : Mat n) *ᵥ w = v := by dsimp only [w]; rw [mulVec_mulVec,hUs,one_mulVec]
    rw [← he,hz,mulVec_zero]
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hw0 (funext hh)
  have hei := congrFun hw i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hei
  have ha : hA.isHermitian.eigenvalues i = a := Complex.ofReal_injective (mul_right_cancel₀ hi hei)
  exact ha ▸ hA.eigenvalues_pos i

#print axioms eigenvalue_positive
end NLA.MI22.Commuting
