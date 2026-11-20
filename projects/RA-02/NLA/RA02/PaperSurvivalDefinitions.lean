module

public import NLA.RA02.PaperHistoryDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA02.Paper

def SurvivingHistory {r : ℕ} (h : Fin r ↪ Fin (r+1)) : Prop :=
  ∀ s : Fin r, s.castSucc ∉ Set.range (historyPrefix h s.isLt.le)

def historyIndicator {r : ℕ} (h : Fin r ↪ Fin (r+1)) : ℝ :=
  ∏ s : Fin r, if s.castSucc ∉ Set.range (historyPrefix h s.isLt.le) then 1 else 0

end NLA.RA02.Paper
