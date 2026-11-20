module

public import NLA.TR27.ProjectiveGeometry
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The complement of a homogeneous equation is a projective principal open. -/
theorem homogeneous_zero_set_closed (X : ProjectiveVariety W)
    (f : MvPolynomial (Fin X.dimension) ℂ) (d : ℕ) (hf : f.IsHomogeneous d) :
    X.IsClosed {p | MvPolynomial.eval (X.coordinates p.rep) f = 0} := by
  apply Set.Subset.antisymm
  · intro p hp
    exact hp f d hf (fun q hq => hq)
  · exact zariskiClosure_subset X _

/-- A nonempty principal open of the actual irreducible point set is dense,
with density expressed by the same homogeneous-polynomial closure as rank. -/
theorem principal_open_dense (X : ProjectiveVariety W) (hX : X.Admissible)
    (g : MvPolynomial (Fin X.dimension) ℂ) (e : ℕ) (hg : g.IsHomogeneous e)
    (hne : ∃ p ∈ X.points, MvPolynomial.eval (X.coordinates p.rep) g ≠ 0) :
    X.zariskiClosure {p | p ∈ X.points ∧ MvPolynomial.eval (X.coordinates p.rep) g ≠ 0} =
      X.points := by
  apply Set.Subset.antisymm
  · have hm := zariskiClosure_mono X
      (show {p | p ∈ X.points ∧ MvPolynomial.eval (X.coordinates p.rep) g ≠ 0} ⊆
        X.points from fun _ h => h.1)
    rw [admissible_points_closed X hX] at hm
    exact hm
  · intro p hp f d hf hfU
    have hprod : f*g ∈ X.ideal := by
      apply homogeneous_mem_ideal_of_vanishes X hX (f*g) (d+e) (hf.mul hg)
      intro q hq
      rw [map_mul]
      by_cases hz : MvPolynomial.eval (X.coordinates q.rep) g = 0
      · rw [hz, mul_zero]
      · rw [hfU q ⟨hq,hz⟩, zero_mul]
    rcases hX.2.1.mem_or_mem hprod with hfi | hgi
    · exact hp f hfi
    · obtain ⟨q,hq,hqg⟩ := hne
      exact (hqg (hq g hgi)).elim

#print axioms principal_open_dense
end NLA.TR27.Paper
