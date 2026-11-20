module

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Actual cyclic windows of the tied sorted Gram eigenspace. Pure definitions.
Reference extension of OpenProblemsInNLA MI13/TR04, Apache2 attribution retained.
Copyright (c) 2026 George Stepaniants. New formalization by Codex. -/
public import NLA.TR04.OptimalityEquality.CountDefinitions
public import Mathlib.Algebra.Group.Fin.Basic
public import NLA.TR04.OrderedTensorSolver.IndexDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.OrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix BigOperators

def EIndex {m n : ℕ} (A : Rect m n) (tau : ℝ) :=
  {i : Fin m // singularValue A.transpose i.val=tau}
def HIndex {m n : ℕ} (A : Rect m n) (tau : ℝ) :=
  {i : Fin m // tau<singularValue A.transpose i.val}
noncomputable instance eFinite {m n : ℕ} (A : Rect m n) (tau : ℝ) : Fintype (EIndex A tau) := by
  classical
  exact inferInstanceAs (Fintype {i : Fin m // singularValue A.transpose i.val=tau})
noncomputable instance hFinite {m n : ℕ} (A : Rect m n) (tau : ℝ) : Fintype (HIndex A tau) := by
  classical
  exact inferInstanceAs (Fintype {i : Fin m // tau<singularValue A.transpose i.val})
def eCount {m n : ℕ} (A : Rect m n) (tau : ℝ) := Fintype.card (EIndex A tau)
def hCount {m n : ℕ} (A : Rect m n) (tau : ℝ) := Fintype.card (HIndex A tau)
def boundaryOrdinal {m n : ℕ} (A : Rect m n) (tau : ℝ) := Reference.OrderedIndex.indexEnum (fun i : Fin m => singularValue A.transpose i.val=tau)
def inWindow {t : ℕ} (s : ℕ) (j i : Fin t) : Prop := (i-j).val<s

def windowSelected {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) (i : Fin m) : Prop :=
  if he : singularValue A.transpose i.val=tau then
    inWindow s j (boundaryOrdinal A tau ⟨i,he⟩) else False
def selected {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) (i : Fin m) : Prop :=
  tau<singularValue A.transpose i.val ∨ windowSelected A tau s j i

def indicator {m : ℕ} (p : Fin m → Prop) : Fin m → ℝ := fun i => if p i then 1 else 0
def indicatorProjector {m : ℕ} (V : Square m) (p : Fin m → Prop) : Square m :=
  V * Matrix.diagonal (indicator p) * V.transpose
def indicatorFrame {m : ℕ} (V : Square m) (p : Fin m → Prop) :
    Rect m (Fintype.card {i : Fin m // p i}) :=
  V.submatrix id (fun j => ((Reference.OrderedIndex.indexEnum p).symm j).val)
def windowProjector {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) : Square m :=
  indicatorProjector (leftVectorMatrix A) (windowSelected A tau s j)
def candidateProjector {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) : Square m :=
  indicatorProjector (leftVectorMatrix A) (selected A tau s j)
def candidateFrame {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) :=
  indicatorFrame (leftVectorMatrix A) (selected A tau s j)

end
end Reference.OrderedCyclicBoundary