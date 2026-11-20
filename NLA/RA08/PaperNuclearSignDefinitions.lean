module

public import NLA.RA08.PaperNuclearDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def realSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

end NLA.RA08.Paper
