module

public import NLA.MF05.Definitions

@[expose] public section

/- Real-matrix semantics and the entrywise complex embedding; no claims assumed. -/
set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper

abbrev RealSquare (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev RealVector (d : ℕ) := EuclideanSpace ℝ (Fin d)

def complexify {d : ℕ} : RealSquare d →+* NLA.MF07.Square d :=
  Complex.ofRealHom.mapMatrix

def realSpectralNorm {d : ℕ} (A : RealSquare d) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜:=ℝ) A‖

def realMatrixProduct {d : ℕ} (w : List (RealSquare d)) : RealSquare d := w.reverse.prod
def realWordNorms {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) : Set ℝ :=
  {r | ∃ w : List (RealSquare d), w.length = n ∧ (∀ A ∈ w, A ∈ M) ∧
    r = realSpectralNorm (realMatrixProduct w)}
def realFamilyGrowth {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) := sSup (realWordNorms M n)
def realRootGrowth {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) :=
  Real.rpow (realFamilyGrowth M n) (1/(n:ℝ))
def realRadius {d : ℕ} (M : Set (RealSquare d)) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = realRootGrowth M n}

def realPointDistance {d : ℕ} (A : RealSquare d) (N : Set (RealSquare d)) : ℝ :=
  sInf ((fun B => realSpectralNorm (A-B)) '' N)
def realDirectedDistance {d : ℕ} (M N : Set (RealSquare d)) : ℝ :=
  sSup ((fun A => realPointDistance A N) '' M)
def realHausdorff {d : ℕ} (M N : Set (RealSquare d)) : ℝ :=
  max (realDirectedDistance M N) (realDirectedDistance N M)

end NLA.MF05.Paper
