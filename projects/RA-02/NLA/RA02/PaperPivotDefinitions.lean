module

public import NLA.RA02.PaperResidualDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- The real rank-one pivot update. Division by zero leaves the matrix unchanged. -/
def crossUpdate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i j - A i q * A p j / A p q

def complexify {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (A i j : ℂ)

def realCholeskyPath {n : ℕ} : Matrix (Fin n) (Fin n) ℝ → List (Fin n) → Matrix (Fin n) (Fin n) ℝ
  | A, [] => A
  | A, j :: w => realCholeskyPath (crossUpdate A j j) w

def realLUNext {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Option (Fin n × Fin n) → Matrix (Fin n) (Fin n) ℝ
  | none => 0
  | some ij => crossUpdate A ij.1 ij.2

def realLUPath {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    {k : ℕ} → (Fin k → Option (Fin n × Fin n)) → Matrix (Fin n) (Fin n) ℝ
  | 0, _ => A
  | k+1, h => realLUPath (realLUNext A (h 0)) (fun i : Fin k => h i.succ)

def realLUListPath {n : ℕ} : Matrix (Fin n) (Fin n) ℝ → List (Option (Fin n × Fin n)) → Matrix (Fin n) (Fin n) ℝ
  | A, [] => A
  | A, p :: w => realLUListPath (realLUNext A p) w

end NLA.RA02.Paper
