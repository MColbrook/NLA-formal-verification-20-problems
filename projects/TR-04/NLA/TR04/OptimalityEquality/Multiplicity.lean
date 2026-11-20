module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual finite fully-retained-boundary bridge for main.tex lem:tr04-equality.
Extends real MI-13/RA02 at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.Boundary
public import NLA.TR04.OptimalityEquality.MultiplicityDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage

theorem strict_gap_of_full_boundary_multiplicity {m n : ℕ} (A : Rect m n)
    (r : ℕ) (hrank : r < A.rank)
    (hcount : retainedBoundaryMultiplicity A r =
      boundaryMultiplicity A (singularValue A (r-1))) :
    singularValue A r < singularValue A (r-1) := by
  classical
  have hrm : r < m := hrank.trans_le (Matrix.rank_le_height A)
  let i : Fin m := ⟨r, hrm⟩
  let T := Finset.univ.filter (fun j : Fin m =>
    singularValue A.transpose j.val = singularValue A (r-1))
  let S := T.filter (fun j => j.val < r)
  have hcard : S.card = T.card := hcount
  have hST : S = T := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard.ge
  have hle : singularValue A r ≤ singularValue A (r-1) :=
    (singular_values_semantics A).2.1 (Nat.sub_le r 1)
  by_contra hh
  have he : singularValue A r = singularValue A (r-1) :=
    le_antisymm hle (le_of_not_gt hh)
  have hi : i ∈ T := by simp [T, i, singularValue_transpose, he]
  rw [← hST] at hi
  have hir : i.val < r := (Finset.mem_filter.mp hi).2
  dsimp [i] at hir
  omega

theorem left_full_boundary_annihilates_best_rank_residual_of_full_multiplicity
    {m n : ℕ} (A B : Rect m n) (r : ℕ) (hr : 0 < r) (hrank : r < A.rank)
    (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C))
    (hcount : retainedBoundaryMultiplicity A r =
      boundaryMultiplicity A (singularValue A (r-1))) :
    (leftAboveProjector A (singularValue A (r-1)) +
      leftBoundaryProjector A (singularValue A (r-1))) * (A-B) = 0 :=
  left_full_boundary_annihilates_best_rank_residual_of_rank_gt A B r hr hrank hB hbest
    (strict_gap_of_full_boundary_multiplicity A r hrank hcount)

#print axioms strict_gap_of_full_boundary_multiplicity
#print axioms left_full_boundary_annihilates_best_rank_residual_of_full_multiplicity
end
end Reference.RealOptimalityEquality
