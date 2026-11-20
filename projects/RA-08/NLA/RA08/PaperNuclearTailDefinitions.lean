module

public import NLA.RA08.PaperNuclearNystromDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearLiftTailLower (η t : ℝ) : ℝ := (1-η)*t-2*η*(1-η)*t^2

/-- The infimum of the actual finite real spectrum. -/
def nuclearLiftSmallest (m : ℕ) (η t : ℝ) : ℝ :=
  sInf (spectrum ℝ (nuclearLiftA m η t))

end NLA.RA08.Paper
