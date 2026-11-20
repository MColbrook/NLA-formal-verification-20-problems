module

public import NLA.RA02.PaperSharpDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace NLA.RA02.Paper

abbrev MissingColumn {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :=
  {j : Fin s // Fin.castLE hs j ∉ Set.range rows}

abbrev OutsideRow {n s : ℕ} (rows : Fin s ↪ Fin n) :=
  {i : Fin s // s ≤ (rows i).val}

/-- Column-normalized prefix, extended polynomially to t=0. -/
def normalizedPrefix {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Matrix (Fin s) (Fin s) ℝ := fun i j =>
  if Fin.castLE hs j ∉ Set.range rows then
    if Fin.castLE hs j < rows i then ((rows i).val+j.val+2 : ℝ)⁻¹ else 0
  else lower n t (rows i) (Fin.castLE hs j)

end NLA.RA02.Paper
