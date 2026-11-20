module

public import NLA.MF05.PaperGrowth
public import Mathlib.Topology.NhdsWithin

@[expose] public section

/- Passing to closure preserves the actual word supremum, not merely a
surrogate radius. This extends the compact-family infrastructure to all
nonempty bounded families in the paper. -/
set_option autoImplicit false
open NLA.MF07 Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MF05.Paper

lemma wordNorms_mono {d n : ℕ} {M N : Set (Square d)} (h : M ⊆ N) :
    wordNorms M n ⊆ wordNorms N n := by
  rintro r ⟨w, hw, hM, rfl⟩
  exact ⟨w, hw, fun A hA => h (hM A hA), rfl⟩

theorem complex_closure_growth {d : ℕ} (M : Set (Square d))
    (hM : Bornology.IsBounded M) (hne : M.Nonempty) (n : ℕ) :
    familyGrowth (closure M) n = familyGrowth M n := by
  have hc := hM.isCompact_closure
  have hce := hne.mono subset_closure
  have hb := (wordNorms_compact (closure M) hc n).bddAbove
  have hsub : wordNorms M n ⊆ wordNorms (closure M) n := wordNorms_mono subset_closure
  have hbM : BddAbove (wordNorms M n) := hb.mono hsub
  apply le_antisymm
  · have hf : Continuous (fun A : Fin n → Square d => spectralNorm (finiteProduct A)) :=
      continuous_spectralNorm.comp continuous_finiteProduct
    have hclosed : IsClosed {A : Fin n → Square d |
        spectralNorm (finiteProduct A) ≤ familyGrowth M n} := isClosed_le hf continuous_const
    have hbase : Set.pi Set.univ (fun _ : Fin n => M) ⊆
        {A : Fin n → Square d | spectralNorm (finiteProduct A) ≤ familyGrowth M n} := by
      intro A hA
      apply le_csSup hbM
      exact ⟨List.ofFn A, List.length_ofFn, WordIn_ofFn M A (fun i => hA i (by simp)), rfl⟩
    have hclosure := closure_minimal hbase hclosed
    rw [closure_pi_set] at hclosure
    apply csSup_le (wordNorms_nonempty (closure M) hce n)
    intro r hr
    rw [wordNorms_eq_range] at hr
    obtain ⟨A, rfl⟩ := hr
    exact hclosure (fun i _ => (A i).property)
  · exact csSup_le_csSup hb (wordNorms_nonempty M hne n) hsub

theorem complex_closure_radius {d : ℕ} (M : Set (Square d))
    (hM : Bornology.IsBounded M) (hne : M.Nonempty) :
    jointSpectralRadius (closure M) = jointSpectralRadius M := by
  simp only [jointSpectralRadius, rootGrowth, complex_closure_growth M hM hne]

theorem complex_bounded_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : Bornology.IsBounded M) (hne : M.Nonempty) :
    Tendsto (rootGrowth M) atTop (𝓝 (jointSpectralRadius M)) := by
  have h := complex_root_limit hd (closure M) hM.isCompact_closure (hne.mono subset_closure)
  have he : rootGrowth (closure M) = rootGrowth M := by
    funext n
    simp only [rootGrowth, complex_closure_growth M hM hne]
  rwa [he, complex_closure_radius M hM hne] at h

lemma complex_closure_normBall {d : ℕ} (M : Set (Square d)) (L : ℝ)
    (hML : InNormBall M L) : InNormBall (closure M) L := by
  exact closure_minimal hML (isClosed_le continuous_spectralNorm continuous_const)

theorem complex_bounded_positive_radius_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (hr : 0 < jointSpectralRadius M) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) *
      (jointSpectralRadius M)^((n : ℤ)-(d : ℤ)+1) := by
  have h := complex_positive_radius_growth hd (closure M) hM.isCompact_closure
    (hne.mono subset_closure) L hL (complex_closure_normBall M L hML)
    (by rwa [complex_closure_radius M hM hne]) n hn
  simpa only [complex_closure_growth M hM hne, complex_closure_radius M hM hne] using h

theorem complex_bounded_zero_radius_nilpotent {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hr : jointSpectralRadius M = 0)
    (w : List (Square d)) (hw : WordIn M w) (hlen : d ≤ w.length) : matrixProduct w = 0 := by
  exact complex_zero_radius_nilpotent hd (closure M) hM.isCompact_closure
    (hne.mono subset_closure) L hL (complex_closure_normBall M L hML)
    (by rwa [complex_closure_radius M hM hne]) w
    (fun A hA => subset_closure (hw A hA)) hlen

lemma complexify_bounded {d : ℕ} (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) :
    Bornology.IsBounded (complexify '' M) :=
  (hM.isCompact_closure.image continuous_complexify).isBounded.subset
    (Set.image_mono subset_closure)

theorem real_bounded_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (RealSquare d))
    (hM : Bornology.IsBounded M) (hne : M.Nonempty) :
    Tendsto (realRootGrowth M) atTop (𝓝 (realRadius M)) := by
  have h := complex_bounded_root_limit hd (complexify '' M) (complexify_bounded M hM)
    (hne.image complexify)
  have he : rootGrowth (complexify '' M) = realRootGrowth M := funext (complexify_rootGrowth M)
  rwa [he, complexify_radius] at h

theorem real_bounded_positive_radius_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (hr : 0 < realRadius M) (n : ℕ) (hn : 1 ≤ n) :
    realFamilyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) *
      (realRadius M)^((n : ℤ)-(d : ℤ)+1) := by
  have h := complex_bounded_positive_radius_growth hd (complexify '' M)
    (complexify_bounded M hM) (hne.image complexify) L hL (complexify_normBall M L hML)
    (by rwa [complexify_radius]) n hn
  simpa only [complexify_growth, complexify_radius] using h

theorem real_bounded_zero_radius_nilpotent {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hr : realRadius M = 0)
    (w : List (RealSquare d)) (hw : ∀ A ∈ w, A ∈ M) (hlen : d ≤ w.length) :
    realMatrixProduct w = 0 := by
  have hwc : WordIn (complexify '' M) (w.map complexify) := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    exact ⟨A, hw A hA, rfl⟩
  have h := complex_bounded_zero_radius_nilpotent hd (complexify '' M)
    (complexify_bounded M hM) (hne.image complexify) L hL (complexify_normBall M L hML)
    (by rwa [complexify_radius]) (w.map complexify) hwc (by simpa using hlen)
  rw [complexify_product] at h
  ext i j
  have he := congrArg (fun A : Square d => (A i j).re) h
  simpa [complexify] using he

#print axioms complex_bounded_positive_radius_growth
#print axioms complex_bounded_zero_radius_nilpotent
#print axioms real_bounded_positive_radius_growth
#print axioms real_bounded_zero_radius_nilpotent
#print axioms complex_bounded_root_limit
#print axioms real_bounded_root_limit
end NLA.MF05.Paper
