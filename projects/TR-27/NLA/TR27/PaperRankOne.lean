module

public import NLA.TR27.ProjectiveGeometry
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem rank_at_most_one_iff_mem (X : ProjectiveVariety W) (hX : X.Admissible)
    (p : ℙ ℂ W) : ProjectiveRankAtMost X.points 1 p ↔ p ∈ X.points := by
  constructor
  · intro hp
    have hc : ConeRankAtMost X.cone 1 p.rep := by
      apply (projective_cone_rank X hX 1 p.rep p.rep_nonzero).mp
      simpa only [p.mk_rep] using hp
    obtain ⟨k, hk, a, x, hx, heq⟩ := hc
    change p.rep ∈ X.cone
    cases k with
    | zero =>
      simp only [Fin.sum_univ_zero] at heq
      exact (p.rep_nonzero heq).elim
    | succ k =>
      have hk0 : k = 0 := by omega
      subst k
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at heq
      rw [heq]
      exact cone_smul X hX (a 0) (x 0) (hx 0)
  · intro hp
    refine ⟨1, le_rfl, fun _ => p, fun _ => hp, ?_⟩
    exact Projectivization.Subspace.subset_span _ (Set.mem_range.mpr ⟨0, rfl⟩)

theorem rank_one_closure_eq_points (X : ProjectiveVariety W) (hX : X.Admissible) :
    X.zariskiClosure {q | ProjectiveRankAtMost X.points 1 q} = X.points := by
  have hset : {q | ProjectiveRankAtMost X.points 1 q} = X.points := by
    ext q
    exact rank_at_most_one_iff_mem X hX q
  rw [hset]
  exact admissible_points_closed X hX

theorem border_rank_one_iff_mem (X : ProjectiveVariety W) (hX : X.Admissible)
    (p : ℙ ℂ W) : borderRank X p ≤ 1 ↔ p ∈ X.points := by
  rw [← (rank_minima X hX p).2.2.2 1, rank_one_closure_eq_points X hX]

theorem border_rank_lower_two (X : ProjectiveVariety W) (hX : X.Admissible)
    (p : ℙ ℂ W) (hp : p ∉ X.points) : 2 ≤ borderRank X p := by
  have hn : ¬ borderRank X p ≤ 1 := by
    intro h
    exact hp ((border_rank_one_iff_mem X hX p).mp h)
  omega

#print axioms border_rank_one_iff_mem
#print axioms border_rank_lower_two
end NLA.TR27.Paper
