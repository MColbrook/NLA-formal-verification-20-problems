module

public import NLA.MF12.Definitions

@[expose] public section

set_option autoImplicit false
namespace NLA.MF12.Paper

/-- An actual integer divided by a nonnegative power of two. -/
def IsDyadic (x : ℝ) : Prop := ∃ (z : ℤ) (k : ℕ), x = (z : ℝ)/(2 : ℝ)^k

end NLA.MF12.Paper
