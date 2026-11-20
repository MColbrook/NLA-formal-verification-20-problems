module

public import NLA.RA02.PaperHistoryDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA02.Paper

def historyTraceNormalizer {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin k ↪ Fin n) (s : Fin k) : ℝ :=
  (interpolatoryResidual A (historyPrefix h s.isLt.le) (historyPrefix h s.isLt.le)).trace

def historyFrobeniusNormalizer {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin k ↪ Fin n) (s : Fin k) : ℝ :=
  ∑ i, ∑ j, (interpolatoryResidual A
    (historyPrefix rows s.isLt.le) (historyPrefix cols s.isLt.le) i j)^2

end NLA.RA02.Paper
