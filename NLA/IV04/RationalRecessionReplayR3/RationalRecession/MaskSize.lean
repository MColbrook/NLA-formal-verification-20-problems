module

public import NLA.IV04.RationalRecessionReplayR3.PureDefinitions
/- Reduced size bound for an actual nonzero integer row-mask Gram candidate. -/
public import NLA.IV04.RationalRecessionReplayR3.RationalRecession.Threshold
public import NLA.IV04.PolyhedronSupportReplayR3.OriginalObjectiveAttainment.IntegerAttainment

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04RationalRecessionRay
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem integer_mask_candidate_reduced_size
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (I : Finset ι) (H : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (hne : originalMaskCandidate (integerRationalMatrix A) (integerRationalVector b) I ≠ 0) :
    ∀ j,
      (originalMaskCandidate (integerRationalMatrix A) (integerRationalVector b) I j).den ≤
        gramCertificateBound (Fintype.card ι) n H ∧
      (originalMaskCandidate (integerRationalMatrix A) (integerRationalVector b) I j).num.natAbs ≤
        gramCertificateBound (Fintype.card ι) n H := by
  classical
  let M : Matrix ι (Fin n) ℤ := fun i j => if i ∈ I then A i j else 0
  let v : ι → ℤ := fun i => if i ∈ I then b i else 0
  let G := Mᵀ*M
  let c := Mᵀ *ᵥ v
  let q := originalMaskCandidate (integerRationalMatrix A) (integerRationalVector b) I
  have hM : maskedMatrix (integerRationalMatrix A) I=integerRationalMatrix M := by
    ext i j
    change (if i ∈ I then (A i j : ℚ) else 0)=
      ((if i ∈ I then A i j else 0 : ℤ) : ℚ)
    by_cases hi : i ∈ I <;> simp [hi]
  have hv : maskedBounds (integerRationalVector b) I=integerRationalVector v := by
    funext i
    by_cases hi : i ∈ I <;> simp [maskedBounds,integerRationalVector,v,hi]
  have hG : (integerRationalMatrix M)ᵀ*integerRationalMatrix M=integerRationalMatrix G := by
    change (Mᵀ.map (Int.castRingHom ℚ))*(M.map (Int.castRingHom ℚ))=
      (Mᵀ*M).map (Int.castRingHom ℚ)
    exact Matrix.map_mul.symm
  have hc : integerRationalVector c=(integerRationalMatrix M)ᵀ *ᵥ integerRationalVector v := by
    funext i
    exact (Int.castRingHom ℚ).map_mulVec Mᵀ v i
  have hq : q=cramerCandidate (integerRationalMatrix G) (integerRationalVector c) := by
    dsimp [q]
    unfold originalMaskCandidate
    rw [hM,hv,hG,← hc]
  have hcast : (G.det : ℚ)=(integerRationalMatrix G).det := (Int.castRingHom ℚ).map_det G
  have hd : G.det ≠ 0 := by
    intro hz
    apply hne
    change q=0
    funext j
    rw [hq]
    simp [cramerCandidate,← hcast,hz]
  have hcoords (j : Fin n) : q j=(((G.updateCol j c).det : ℤ) : ℚ)/(G.det : ℚ) := by
    rw [hq,cramerCandidate_coordinate,← hcast]
    have hnum : (((G.updateCol j c).det : ℤ) : ℚ)=
        ((integerRationalMatrix G).updateCol j (integerRationalVector c)).det := by
      calc
        _ = (integerRationalMatrix (G.updateCol j c)).det := (Int.castRingHom ℚ).map_det _
        _ = _ := by
          congr 1
          exact Matrix.map_updateCol (Int.castRingHom ℚ)
    rw [← hnum]
  have hMH : ∀ i j, |M i j| ≤ (H : ℤ) := by
    intro i j
    dsimp [M]
    split_ifs
    · exact hA i j
    · simp
  have hvH : ∀ i, |v i| ≤ (H : ℤ) := by
    intro i
    dsimp [v]
    split_ifs
    · exact hb i
    · simp
  have hbounds := integer_gram_cramer_bounds M v H hMH hvH
  intro j
  exact ⟨rational_den_le_of_integer_fraction (q j) (G.updateCol j c).det G.det _ hd
      (hcoords j) hbounds.1,
    rational_num_natAbs_le_of_integer_fraction (q j) (G.updateCol j c).det G.det _ hd
      (hcoords j) (hbounds.2 j)⟩

#print axioms integer_mask_candidate_reduced_size
end
end Reference.IV04RationalRecessionRay
