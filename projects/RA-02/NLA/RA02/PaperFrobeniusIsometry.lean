module

public import NLA.RA02.PaperRectangularBestAttainment

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem frobenius_conjTranspose {m n : ℕ} (E : Matrix (Fin m) (Fin n) ℂ) :
    NLA.RA03.frobeniusSq E.conjTranspose = NLA.RA03.frobeniusSq E := by
  rw [lu_frobeniusSq_eq_gram_trace,lu_frobeniusSq_eq_gram_trace,Matrix.conjTranspose_conjTranspose]
  unfold NLA.RA02.realTrace
  exact congrArg Complex.re (Matrix.trace_mul_comm E E.conjTranspose)

theorem frobenius_isometry_left {M m n : ℕ} (P : Matrix (Fin M) (Fin m) ℂ)
    (hP : P.conjTranspose*P=1) (E : Matrix (Fin m) (Fin n) ℂ) :
    NLA.RA03.frobeniusSq (P*E)=NLA.RA03.frobeniusSq E := by
  rw [lu_frobeniusSq_eq_gram_trace,lu_frobeniusSq_eq_gram_trace]
  have he : (P*E).conjTranspose*(P*E)=E.conjTranspose*(P.conjTranspose*P)*E := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [he,hP,Matrix.mul_one]

theorem frobenius_isometry_right {m n N : ℕ} (P : Matrix (Fin N) (Fin n) ℂ)
    (hP : P.conjTranspose*P=1) (E : Matrix (Fin m) (Fin n) ℂ) :
    NLA.RA03.frobeniusSq (E*P.conjTranspose)=NLA.RA03.frobeniusSq E := by
  have ht : (E*P.conjTranspose).conjTranspose=P*E.conjTranspose := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [← frobenius_conjTranspose (E*P.conjTranspose),ht,
    frobenius_isometry_left P hP,frobenius_conjTranspose E]

theorem frobenius_right_compression_le {m N n : ℕ}
    (E : Matrix (Fin m) (Fin N) ℂ) (P : Matrix (Fin N) (Fin n) ℂ)
    (hP : P.conjTranspose*P=1) :
    NLA.RA03.frobeniusSq (E*P) ≤ NLA.RA03.frobeniusSq E := by
  rw [lu_frobeniusSq_eq_gram_trace (E*P)]
  have he : (E*P).conjTranspose*(E*P)=P.conjTranspose*(E.conjTranspose*E)*P := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [he]
  exact frobenius_compression_bound E P hP

theorem frobenius_left_compression_le {N m n : ℕ}
    (P : Matrix (Fin N) (Fin m) ℂ) (hP : P.conjTranspose*P=1)
    (E : Matrix (Fin N) (Fin n) ℂ) :
    NLA.RA03.frobeniusSq (P.conjTranspose*E) ≤ NLA.RA03.frobeniusSq E := by
  have ht : (P.conjTranspose*E).conjTranspose=E.conjTranspose*P := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [← frobenius_conjTranspose (P.conjTranspose*E),ht]
  exact (frobenius_right_compression_le E.conjTranspose P hP).trans_eq (frobenius_conjTranspose E)

theorem frobenius_isometric_embedding {n N : ℕ} (P : Matrix (Fin N) (Fin n) ℂ)
    (hP : P.conjTranspose*P=1) (E : NLA.RA02.Square n) :
    NLA.RA03.frobeniusSq (P*E*P.conjTranspose)=NLA.RA03.frobeniusSq E := by
  rw [frobenius_isometry_right P hP,frobenius_isometry_left P hP]

theorem frobenius_double_compression_le {n N : ℕ} (P : Matrix (Fin N) (Fin n) ℂ)
    (hP : P.conjTranspose*P=1) (E : NLA.RA02.Square N) :
    NLA.RA03.frobeniusSq (P.conjTranspose*E*P) ≤ NLA.RA03.frobeniusSq E :=
  (frobenius_right_compression_le (P.conjTranspose*E) P hP).trans
    (frobenius_left_compression_le P hP E)

#print axioms frobenius_double_compression_le
end NLA.RA02.Paper
