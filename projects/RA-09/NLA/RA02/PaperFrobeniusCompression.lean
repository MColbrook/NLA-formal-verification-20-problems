module

public import NLA.RA02.PaperLUProcess

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem frobenius_compression_bound {m n q : ℕ} (E : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin q) ℂ) (hU : U.conjTranspose*U = 1) :
    (U.conjTranspose*(E.conjTranspose*E)*U).trace.re ≤ NLA.RA03.frobeniusSq E := by
  have hP := (frame_complement_posSemidef U hU).mul_mul_conjTranspose_same E
  have hn := (Complex.nonneg_iff.mp hP.trace_nonneg).1
  have he : (E*(1-U*U.conjTranspose)*E.conjTranspose).trace =
      (E.conjTranspose*E).trace - (U.conjTranspose*(E.conjTranspose*E)*U).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub]
    congr 1
    · exact Matrix.trace_mul_comm E E.conjTranspose
    · calc
        _ = ((E*U)*(U.conjTranspose*E.conjTranspose)).trace := by simp only [Matrix.mul_assoc]
        _ = ((U.conjTranspose*E.conjTranspose)*(E*U)).trace :=
          Matrix.trace_mul_comm (E*U) (U.conjTranspose*E.conjTranspose)
        _ = _ := by simp only [Matrix.mul_assoc]
  rw [he, Complex.sub_re] at hn
  rw [lu_frobeniusSq_eq_gram_trace]
  exact sub_nonneg.mp hn

#print axioms frobenius_compression_bound
end NLA.RA02.Paper
