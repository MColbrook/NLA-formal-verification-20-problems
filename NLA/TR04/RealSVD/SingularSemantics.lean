module

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.
Real adaptation of MI-13 at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
-/
public import NLA.TR04.RealSVD.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace Reference.RealSVDPackage
noncomputable section

theorem singular_values_semantics {m n : ℕ} (A : Rect m n) :
    (∀ k, 0 ≤ singularValue A k) ∧ Antitone (singularValue A) ∧
    ∀ k, n ≤ k → singularValue A k = 0 := by
  refine ⟨(euclideanLin A).singularValues_nonneg,
    (euclideanLin A).singularValues_antitone, ?_⟩
  intro k hk
  exact (euclideanLin A).singularValues_of_finrank_le (by simpa using hk)

theorem singular_values_gram {m n : ℕ} (A : Rect m n) (i : Fin n) :
    singularValue A i.val ^ 2 = gramEigenvalue A i := by
  exact (euclideanLin A).sq_singularValues_fin
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) i

#print axioms singular_values_semantics
#print axioms singular_values_gram

end
end Reference.RealSVDPackage

