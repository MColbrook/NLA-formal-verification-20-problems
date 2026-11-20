module

public import NLA.MD06.CubicConfiguration.Definitions
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Mul

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration
attribute [local instance] Classical.propDecidable

noncomputable def MatchingMatrix {n : ℕ} (p : Pairing n) : Matrix (Dart n) (Dart n) ℝ :=
  fun a b => if p.val a=b then 1 else 0

noncomputable def IncidenceMatrix (n : ℕ) : Matrix (Fin n) (Dart n) ℝ :=
  fun v a => if v=a.1 then 1 else 0

noncomputable def PortMatrix (n : ℕ) : Matrix (Dart n) (Dart n) ℝ :=
  (IncidenceMatrix n).transpose * IncidenceMatrix n - 1

noncomputable def NonbacktrackingMatrix {n : ℕ} (p : Pairing n) : Matrix (Dart n) (Dart n) ℝ :=
  MatchingMatrix p * PortMatrix n

noncomputable def AdjacencyMatrix {n : ℕ} (p : Pairing n) : Matrix (Fin n) (Fin n) ℝ :=
  IncidenceMatrix n * MatchingMatrix p * (IncidenceMatrix n).transpose

end Reference.MD06Nonbacktracking
