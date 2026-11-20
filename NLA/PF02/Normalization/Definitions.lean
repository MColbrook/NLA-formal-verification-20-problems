module

public import NLA.PF02.SupportBridge.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder

def rowSum {p k : ℕ} (A : Fin p → Mat (Fin k)) : Mat (Fin k) := ∑ i, A i

def rootSum {p k : ℕ} (A : Fin p → Mat (Fin k)) : Mat (Fin k) := CFC.sqrt (rowSum A)

def normalizedRow {p k : ℕ} (A : Fin p → Mat (Fin k)) (i : Fin p) : Mat (Fin k) :=
  (rootSum A)⁻¹ * A i * (rootSum A)⁻¹

def normalizedColumn {p q k : ℕ} (A : Fin p → Mat (Fin k))
    (B : Fin q → Mat (Fin k)) (j : Fin q) : Mat (Fin k) :=
  rootSum A * B j * rootSum A
end Reference.PF02Normalization
