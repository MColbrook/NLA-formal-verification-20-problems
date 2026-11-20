module

public import NLA.RA02.PaperLUUpperDefinitions
public import NLA.RA02.PaperLUColumnTail
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem lu_frobeniusSq_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ NLA.RA03.frobeniusSq A := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))

theorem lu_frobeniusSq_eq_zero_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    NLA.RA03.frobeniusSq A = 0 ↔ A = 0 := by
  constructor
  · intro hz
    ext i j
    apply Complex.normSq_eq_zero.mp
    have h1 : Complex.normSq (A i j) ≤ ∑ b, Complex.normSq (A i b) :=
      Finset.single_le_sum (fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ b, Complex.normSq (A i b)) ≤ NLA.RA03.frobeniusSq A :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _)) (Finset.mem_univ i)
    exact le_antisymm (by simpa [hz] using h1.trans h2) (Complex.normSq_nonneg _)
  · rintro rfl
    simp [NLA.RA03.frobeniusSq]

theorem lu_frobeniusSq_eq_gram_trace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    NLA.RA03.frobeniusSq A = NLA.RA02.realTrace (A.conjTranspose*A) := by
  rw [NLA.RA02.realTrace_eq_sum]
  simp_rw [gram_diagonal_norm, Complex.ofReal_re]
  exact Finset.sum_comm

theorem lu_pivotMass_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (p : NLA.RA03.Pivot m n) : 0 ≤ NLA.RA03.pivotMass A p := by
  cases p with
  | none => simp only [NLA.RA03.pivotMass]; split_ifs <;> norm_num
  | some ij =>
    simp only [NLA.RA03.pivotMass]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (Complex.normSq_nonneg _) (lu_frobeniusSq_nonneg A)

theorem lu_expectedError_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    NLA.RA03.expectedError A 0 = NLA.RA03.frobeniusSq A := by
  simp [NLA.RA03.expectedError, NLA.RA03.historyMass, NLA.RA03.historyResidual]

theorem lu_expectedError_succ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) :
    NLA.RA03.expectedError A (k+1) =
      ∑ p : NLA.RA03.Pivot m n, NLA.RA03.pivotMass A p * NLA.RA03.expectedError (NLA.RA03.nextResidual A p) k := by
  unfold NLA.RA03.expectedError
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => NLA.RA03.Pivot m n)).sum_comp
    (fun h => NLA.RA03.historyMass A h*NLA.RA03.frobeniusSq (NLA.RA03.historyResidual A h)), Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, NLA.RA03.historyMass, NLA.RA03.historyResidual,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]

theorem gramTail_zero {m n : ℕ} (r : ℕ) : gramTail (0 : Matrix (Fin m) (Fin n) ℂ) r = 0 := by
  have h0 : (0 : NLA.RA02.Square n).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (0 : Matrix (Fin m) (Fin n) ℂ)
  unfold gramTail
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul]
  exact rankTail_zero_matrix h0 r

theorem gramTail_zero_rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    gramTail A 0 = NLA.RA03.frobeniusSq A := by
  rw [lu_frobeniusSq_eq_gram_trace, NLA.RA02.trace_eq_sum_ordered _ (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian]
  simp [gramTail, NLA.RA02.rankTail]

#print axioms lu_expectedError_succ
end NLA.RA02.Paper
