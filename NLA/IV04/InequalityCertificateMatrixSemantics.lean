module

public import NLA.IV04.InequalityIntegerBridge
public import NLA.IV04.AffinePolyhedronSteps.IntegerSignedCertificate
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
namespace IV04.Paper.InequalityCertificate

def integerMatrixRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    List (List ℤ × ℤ) := List.ofFn (fun i => (List.ofFn (A i),b i))

def integerVectorList {n : ℕ} (p : Fin n → ℤ) : List ℤ := List.ofFn p

theorem integer_dot_ofFn {n : ℕ} (a p : Fin n → ℤ) :
    inequalityIntegerDot (List.ofFn a) (List.ofFn p)=∑ j, a j*p j := by
  induction n with
  | zero => simp [inequalityIntegerDot]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,inequalityIntegerDot,Fin.sum_univ_succ]
    rw [ih]

theorem matrix_rows_inequalities_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (p : Fin n → ℤ) (d : ℕ) :
    (∀ row ∈ integerMatrixRows A b, row.1.length=(integerVectorList p).length ∧
      inequalityIntegerDot row.1 (integerVectorList p)≤row.2*(d : ℤ)) ↔
      ∀ i, (∑ j, A i j*p j)≤b i*(d : ℤ) := by
  constructor
  · intro h i
    have hi : (List.ofFn (A i),b i) ∈ integerMatrixRows A b := by
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    have hr := (h _ hi).2
    simpa only [integerVectorList,integer_dot_ofFn] using hr
  · intro h row hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    refine ⟨?_,?_⟩
    · simp [integerVectorList]
    · simpa only [integerVectorList,integer_dot_ofFn] using h i

theorem real_matrix_fraction_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (p : Fin n → ℤ) (d : ℕ) (i : Fin m) :
    (integerRealMatrix A *ᵥ (fun j => (p j : ℝ)/(d : ℝ))) i=
      ((∑ j, A i j*p j : ℤ) : ℝ)/(d : ℝ) := by
  simp [integerRealMatrix,Matrix.mulVec,dotProduct,Finset.sum_div,mul_div_assoc]

theorem matrix_fraction_feasible_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (p : Fin n → ℤ) (d : ℕ) (hd : 0<d) :
    feasible (integerRealMatrix A) (integerRealVector b)
      (fun j => (p j : ℝ)/(d : ℝ)) ↔
      ∀ i, (∑ j, A i j*p j)≤b i*(d : ℤ) := by
  unfold feasible
  apply forall_congr'
  intro i
  rw [real_matrix_fraction_sum]
  have hdR : (0 : ℝ)<(d : ℝ) := by exact_mod_cast hd
  change (((∑ j, A i j*p j : ℤ) : ℝ)/(d : ℝ)≤(b i : ℝ)) ↔ _
  rw [div_le_iff₀ hdR]
  norm_cast

theorem integer_matrix_verifier_exact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (p : Fin n → ℤ) (d : ℕ) :
    polynomialInequalitySystemVerifier
      (inequalityIntegerSystemCode (integerMatrixRows A b) (integerVectorList p) d)=[true] ↔
      0<d ∧ feasible (integerRealMatrix A) (integerRealVector b)
        (fun j => (p j : ℝ)/(d : ℝ)) := by
  rw [inequality_integer_system_verifier_exact,matrix_rows_inequalities_iff]
  constructor
  · rintro ⟨hd,hrows⟩
    exact ⟨hd,(matrix_fraction_feasible_iff A b p d hd).mpr hrows⟩
  · rintro ⟨hd,hfeasible⟩
    exact ⟨hd,(matrix_fraction_feasible_iff A b p d hd).mp hfeasible⟩

#print axioms integer_dot_ofFn
#print axioms matrix_rows_inequalities_iff
#print axioms real_matrix_fraction_sum
#print axioms matrix_fraction_feasible_iff
#print axioms integer_matrix_verifier_exact
end IV04.Paper.InequalityCertificate
