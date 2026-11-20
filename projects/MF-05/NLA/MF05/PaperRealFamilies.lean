module

public import NLA.MF05.PaperRealNorm
public import NLA.MF05.RootLimit

@[expose] public section

set_option autoImplicit false
open scoped Topology
open NLA.MF07 Filter
noncomputable section
namespace NLA.MF05.Paper

theorem continuous_complexify {d : ℕ} : Continuous (complexify : RealSquare d → Square d) := by
  change Continuous (fun A : RealSquare d => fun i j => (A i j : ℂ))
  fun_prop

theorem complexify_product {d : ℕ} (w : List (RealSquare d)) :
    matrixProduct (w.map complexify) = complexify (realMatrixProduct w) := by
  simp [matrixProduct, realMatrixProduct, map_list_prod]

theorem complex_word_lift {d : ℕ} (M : Set (RealSquare d)) (w : List (Square d))
    (hw : WordIn (complexify '' M) w) :
    ∃ v : List (RealSquare d), v.map complexify = w ∧ ∀ A ∈ v, A ∈ M := by
  induction w with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons b w ih =>
      obtain ⟨a, ha, hab⟩ := hw b (by simp)
      obtain ⟨v, hv, hvM⟩ := ih (fun B hB => hw B (by simp [hB]))
      refine ⟨a::v, by simp [hab, hv], ?_⟩
      intro A hA
      rcases List.mem_cons.mp hA with hA | hA
      · simpa [hA] using ha
      · exact hvM A hA

theorem complexify_wordNorms {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) :
    wordNorms (complexify '' M) n = realWordNorms M n := by
  ext r
  constructor
  · rintro ⟨w, hwlen, hw, hr⟩
    obtain ⟨v, hv, hvM⟩ := complex_word_lift M w hw
    refine ⟨v, ?_, hvM, ?_⟩
    · have h := congrArg List.length hv
      simpa [hwlen] using h
    · rw [← hv, complexify_product, complexify_spectralNorm] at hr
      exact hr
  · rintro ⟨v, hvlen, hvM, hr⟩
    refine ⟨v.map complexify, by simpa using hvlen, ?_, ?_⟩
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
      exact ⟨A, hvM A hA, rfl⟩
    · simpa only [complexify_product, complexify_spectralNorm] using hr

theorem complexify_growth {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) :
    familyGrowth (complexify '' M) n = realFamilyGrowth M n := by
  unfold familyGrowth realFamilyGrowth
  rw [complexify_wordNorms]

theorem complexify_rootGrowth {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) :
    rootGrowth (complexify '' M) n = realRootGrowth M n := by
  unfold rootGrowth realRootGrowth
  rw [complexify_growth]

theorem complexify_radius {d : ℕ} (M : Set (RealSquare d)) :
    jointSpectralRadius (complexify '' M) = realRadius M := by
  simp only [jointSpectralRadius, realRadius, complexify_rootGrowth]

theorem complexify_pointDistance {d : ℕ} (A : RealSquare d) (N : Set (RealSquare d)) :
    pointFamilyDistance (complexify A) (complexify '' N) = realPointDistance A N := by
  simp only [pointFamilyDistance, realPointDistance, Set.image_image,
    ← map_sub, complexify_spectralNorm]

theorem complexify_directedDistance {d : ℕ} (M N : Set (RealSquare d)) :
    directedSpectralDistance (complexify '' M) (complexify '' N) = realDirectedDistance M N := by
  simp only [directedSpectralDistance, realDirectedDistance, Set.image_image,
    complexify_pointDistance]

theorem complexify_hausdorff {d : ℕ} (M N : Set (RealSquare d)) :
    canonicalHausdorff (complexify '' M) (complexify '' N) = realHausdorff M N := by
  simp only [canonicalHausdorff, realHausdorff, complexify_directedDistance]

theorem real_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (RealSquare d))
    (hM : IsCompact M) (hne : M.Nonempty) :
    Tendsto (realRootGrowth M) atTop (𝓝 (realRadius M)) := by
  have h := (general_root_limit_semantics hd (complexify '' M)
    (hM.image continuous_complexify) (hne.image complexify)).2.2
  have he : rootGrowth (complexify '' M) = realRootGrowth M := funext (complexify_rootGrowth M)
  simpa only [he, complexify_radius] using h

#print axioms complexify_growth
#print axioms complexify_hausdorff
#print axioms real_root_limit
end NLA.MF05.Paper
