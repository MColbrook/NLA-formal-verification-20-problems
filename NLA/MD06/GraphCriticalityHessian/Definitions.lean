module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual
open scoped BigOperators
abbrev Phase (n : ℕ) := Fin n → Real.Angle

def Energy {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then 1 - Real.Angle.cos (theta i - theta j) else 0

def Synchronized {n : ℕ} (theta : Phase n) : Prop := ∀ i j, theta i = theta j

def Gradient {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n) (i : Fin n) : ℝ := by
  classical
  exact ∑ j, if G.Adj i j then Real.Angle.sin (theta i - theta j) else 0

def HessianQuadratic {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n) (z : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then Real.Angle.cos (theta i - theta j) * (z i - z j)^2 else 0

def RealEnergy {n : ℕ} (G : SimpleGraph (Fin n)) (phi : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then 1 - Real.cos (phi i - phi j) else 0

def LineEnergy {n : ℕ} (G : SimpleGraph (Fin n)) (phi z : Fin n → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then 1 - Real.cos (phi i - phi j + t*(z i-z j)) else 0

def LineForce {n : ℕ} (G : SimpleGraph (Fin n)) (phi z : Fin n → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then Real.sin (phi i - phi j + t*(z i-z j)) * (z i-z j) else 0

def LineCurvature {n : ℕ} (G : SimpleGraph (Fin n)) (phi z : Fin n → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then Real.cos (phi i - phi j + t*(z i-z j)) * (z i-z j)^2 else 0

def LaplacianQuadratic {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then (z i-z j)^2 else 0
end Reference.MD06Actual
