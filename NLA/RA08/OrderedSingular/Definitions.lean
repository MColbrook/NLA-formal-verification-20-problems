module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic
public import NLA.RA08.PaperNuclearPolarDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper.OrderedSingular

def indexReindex (m : ℕ) : Fin m ≃ Fin m :=
  (Fin.castOrderIso (Fintype.card_fin m).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m))))

def orderedGram {m : ℕ} (hG : (nuclearTriangularGram m).IsHermitian)
    (j : Fin m) : ℝ :=
  hG.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm j)

def orderedSingular {m : ℕ} (hG : (nuclearTriangularGram m).IsHermitian)
    (j : Fin m) : ℝ := Real.sqrt (orderedGram hG j)

end NLA.RA08.Paper.OrderedSingular
