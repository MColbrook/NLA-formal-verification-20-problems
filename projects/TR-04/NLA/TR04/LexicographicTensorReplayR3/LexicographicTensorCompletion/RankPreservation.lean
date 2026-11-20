module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Every true recursive tensor cut-rank is preserved by arbitrary left multiplication.
The proof recurses through actual grouped/reindexed matrices, not rank contracts.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorCompletion.Regrouping

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage

theorem feasible_mul {m k : ℕ} {ns : List ℕ} (V : Rect k m)
    (A : Tensor m ns) (rs : List ℕ) (hA : feasible m ns A rs) :
    feasible k ns (V*A) rs := by
  induction ns generalizing m k rs with
  | nil => simpa only [feasible] using hA
  | cons n ns ih =>
    cases rs with
    | nil => simp only [feasible] at hA
    | cons r rs =>
      simp only [feasible] at hA ⊢
      refine ⟨(Matrix.rank_mul_le_right V A).trans hA.1, ?_⟩
      rw [merge_mul]
      exact ih (mergeLeft V) (merge A) rs hA.2

theorem feasible_merge_of_cons {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (r : ℕ) (rs : List ℕ) (hA : feasible m (n::ns) A (r::rs)) :
    feasible (rowCount m n) ns (merge A) rs := by
  have h := hA
  simp only [feasible] at h
  exact h.2

#print axioms feasible_mul
end
end Reference.LexTensorCompletion
