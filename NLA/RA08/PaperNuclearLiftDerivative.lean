module

public import NLA.RA08.PaperNuclearLiftDerivativeDefinitions
public import NLA.RA08.PaperNuclearRemainder
public import NLA.RA08.PaperNuclearNystromPositive

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem clippingDividedDifference_symmetric (x y : ℝ) :
    clippingDividedDifference x y=clippingDividedDifference y x := by
  unfold clippingDividedDifference
  by_cases h : x=y
  · subst y; rfl
  · have hy : y ≠ x := Ne.symm h
    simp only [h,hy,↓reduceIte]
    rw [← neg_sub (witnessFunction x) (witnessFunction y),← neg_sub x y,neg_div_neg_eq]

theorem clippingDerivative_isHermitian {n : ℕ} (b : Fin n → ℝ)
    (E : RealMatrix n) (hE : E.IsHermitian) : (clippingDerivative b E).IsHermitian := by
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  have h : E j i=E i j := by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hE i) j
  simp only [Matrix.transpose_apply,clippingDerivative,h,
    clippingDividedDifference_symmetric (b j) (b i)]

theorem nuclearLiftDerivative_prefix (m : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (i j : Fin (m+m)) :
    nuclearLiftDerivative m η i.castSucc j.castSucc=η*nuclearDerivative m i j := by
  simp only [nuclearLiftDerivative,clippingDerivative,nuclearLiftBaseEntries,
    Fin.snoc_castSucc,nuclearLiftPerturbation,Matrix.vecMulVec,Matrix.of_apply,
    nuclearLiftVector,nuclearDerivative,nuclearPerturbation]
  ring_nf
  rw [Real.sq_sqrt hη]
  ring

theorem nuclearLiftDerivative_last (m : ℕ) (η : ℝ) (hη : η ≤ 1) :
    nuclearLiftDerivative m η (Fin.last (m+m)) (Fin.last (m+m))=1-η := by
  simp only [nuclearLiftDerivative,clippingDerivative,nuclearLiftBaseEntries,
    Fin.snoc_last,nuclearLiftPerturbation,Matrix.vecMulVec,Matrix.of_apply,
    nuclearLiftVector]
  norm_num [clippingDividedDifference]
  exact Real.mul_self_sqrt (by linarith)

theorem nuclearLiftDerivative_isHermitian (m : ℕ) (η : ℝ) :
    (nuclearLiftDerivative m η).IsHermitian :=
  clippingDerivative_isHermitian _ _ (nuclearLiftPerturbation_posSemidef m η).isHermitian

theorem nuclearLiftOutput_isHermitian (m : ℕ) (η t : ℝ) :
    (nuclearLiftOutput m η t).IsHermitian := by
  exact (cfc_predicate witnessFunction (nuclearLiftA m η t)).sub
    (cfc_predicate witnessFunction (nuclearLiftBase m))

theorem nuclearLift_nuclear_remainder (m : ℕ) (η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      nuclearNorm (nuclearLiftOutput m η t-t • nuclearLiftDerivative m η) ≤ C*t^2 := by
  simpa only [nuclearLiftOutput,nuclearLiftA,nuclearLiftBase,nuclearLiftDerivative] using
    clipping_nuclear_quadratic_remainder (nuclearLiftBaseEntries m)
      (nuclearLiftBaseEntries_ne_one m) (nuclearLiftPerturbation m η)
      (nuclearLiftPerturbation_posSemidef m η).isHermitian

#print axioms nuclearLift_nuclear_remainder
end NLA.RA08.Paper
