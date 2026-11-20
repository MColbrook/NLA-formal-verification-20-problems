module

public import NLA.MD06.NonbacktrackingFoundation.LiftDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking

noncomputable def TracePolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ) • (LiftCoefficients A t).1 - A * (LiftCoefficients A t).2

def TraceOffsets (n : ℕ) : ℕ → ℝ × ℝ
  | 0 => (n,0)
  | t+1 => ((TraceOffsets n t).2,(TraceOffsets n t).1)

end Reference.MD06Nonbacktracking
