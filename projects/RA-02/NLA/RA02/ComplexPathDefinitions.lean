module

public import NLA.RA02.ComplexHistoryDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA02.Paper.ComplexHistory

def historyTraceNormalizer {n k : ℕ} (A : NLA.RA02.Square n)
    (h : Fin k ↪ Fin n) (s : Fin k) : ℝ :=
  NLA.RA02.realTrace (interpolatoryResidual A (historyPrefix h s.isLt.le) (historyPrefix h s.isLt.le))

def historyFrobeniusNormalizer {n k : ℕ} (A : NLA.RA02.Square n)
    (rows cols : Fin k ↪ Fin n) (s : Fin k) : ℝ :=
  NLA.RA03.frobeniusSq (interpolatoryResidual A
    (historyPrefix rows s.isLt.le) (historyPrefix cols s.isLt.le))

end NLA.RA02.Paper.ComplexHistory
