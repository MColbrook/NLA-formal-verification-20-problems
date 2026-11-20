module

public import NLA.MD06.NonbacktrackingFoundation.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration

noncomputable def LiftMatrix {n : ℕ} (p : Pairing n) : Matrix (Dart n) (Fin n) ℝ :=
  MatchingMatrix p * (IncidenceMatrix n).transpose

noncomputable def VertexPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | 1 => A
  | t+2 => A * VertexPolynomial A (t+1) - (2 : ℝ) • VertexPolynomial A t

noncomputable def LiftCoefficients {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ
  | 0 => (1,0)
  | t+1 => (A * (LiftCoefficients A t).1 - (2 : ℝ) • (LiftCoefficients A t).2,
      (LiftCoefficients A t).1)

end Reference.MD06Nonbacktracking
