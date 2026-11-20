module

public import NLA.MF05.PaperRealDefinitions

@[expose] public section

/- The exact constant in main.tex, without its archive enlargement to 3. -/
set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper

def theta (d : ℕ) : ℝ :=
  if d ≤ 1 then 1 else
    (d : ℝ) * (2 * Real.exp 1 * (d : ℝ)^2 / ((d-1 : ℕ) : ℝ))^(d-1)

end NLA.MF05.Paper
