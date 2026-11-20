module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual singular-subspace multiplicity identities for main.tex lem:tr04-equality.
Extends real MI-13/RA02 at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.Multiplicity
public import NLA.TR04.OptimalityEquality.CountDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage

theorem above_boundary_index_lt_rank_parameter {m n : ℕ} (A : Rect m n)
    (r : ℕ) (i : Fin m) (hi : singularValue A (r-1) < singularValue A.transpose i.val) :
    i.val < r := by
  by_contra hh
  have hle := (singular_values_semantics A.transpose).2.1 (show r-1 ≤ i.val by omega)
  simp only [singularValue_transpose] at hle hi
  exact (not_lt_of_ge hle) hi

theorem retained_boundary_multiplicity_eq_rank_sub_above {m n : ℕ}
    (A : Rect m n) (r : ℕ) (hr : 0 < r) (hrank : r < A.rank) :
    retainedBoundaryMultiplicity A r = r-aboveMultiplicity A (singularValue A (r-1)) := by
  classical
  have hrm : r < m := hrank.trans_le (Matrix.rank_le_height A)
  let T := Finset.univ.filter (fun j : Fin m => j.val < r)
  let H := Finset.univ.filter (fun j : Fin m =>
    singularValue A (r-1) < singularValue A.transpose j.val)
  let S := (Finset.univ.filter (fun j : Fin m =>
    singularValue A.transpose j.val = singularValue A (r-1))).filter (fun j => j.val < r)
  have hcardT : T.card = r := by
    calc
      T.card = (Finset.univ : Finset (Fin r)).card := by
        refine Finset.card_bij (fun (j : Fin m) (hj : j ∈ T) =>
          (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin r)) ?_ ?_ ?_
        · intro j hj
          exact Finset.mem_univ _
        · intro j hj l hl he
          exact Fin.ext (congrArg (fun x : Fin r => x.val) he)
        · intro j hj
          let l : Fin m := ⟨j.val, j.isLt.trans hrm⟩
          have hl : l ∈ T := by simp [T, l, j.isLt]
          exact ⟨l, hl, Fin.ext rfl⟩
      _ = r := by simp
  have hdisj : Disjoint H S := by
    apply Finset.disjoint_left.mpr
    intro j hj hs
    have hlt := (Finset.mem_filter.mp hj).2
    have he := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
    exact (ne_of_lt hlt) he.symm
  have hHS : H ∪ S = T := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, H, S, T]
    constructor
    · rintro (hj | ⟨he, hj⟩)
      · exact above_boundary_index_lt_rank_parameter A r j hj
      · exact hj
    · intro hj
      have hle : singularValue A (r-1) ≤ singularValue A.transpose j.val := by
        simpa only [singularValue_transpose] using
          (singular_values_semantics A.transpose).2.1 (show j.val ≤ r-1 by omega)
      by_cases he : singularValue A.transpose j.val = singularValue A (r-1)
      · exact Or.inr ⟨he, hj⟩
      · exact Or.inl (lt_of_le_of_ne hle (Ne.symm he))
  have hsum : H.card + S.card = r := by
    rw [← Finset.card_union_of_disjoint hdisj, hHS, hcardT]
  change S.card = r-H.card
  omega

theorem left_full_boundary_annihilates_best_rank_residual_of_paper_multiplicities
    {m n : ℕ} (A B : Rect m n) (r : ℕ) (hr : 0 < r) (hrank : r < A.rank)
    (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C))
    (hcount : r-aboveMultiplicity A (singularValue A (r-1)) =
      boundaryMultiplicity A (singularValue A (r-1))) :
    (leftAboveProjector A (singularValue A (r-1)) +
      leftBoundaryProjector A (singularValue A (r-1))) * (A-B) = 0 := by
  apply left_full_boundary_annihilates_best_rank_residual_of_full_multiplicity A B r hr hrank hB hbest
  rw [retained_boundary_multiplicity_eq_rank_sub_above A r hr hrank]
  exact hcount

#print axioms above_boundary_index_lt_rank_parameter
#print axioms retained_boundary_multiplicity_eq_rank_sub_above
#print axioms left_full_boundary_annihilates_best_rank_residual_of_paper_multiplicities
end
end Reference.RealOptimalityEquality
