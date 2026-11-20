module

public import NLA.MF05.PaperCyclicPowers
public import NLA.MF05.PaperRealFamilies

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.MF05.Paper.Cyclic

theorem singleton_word_product {d : ℕ} (A : RealSquare d) (w : List (RealSquare d))
    (hw : ∀ B ∈ w, B ∈ ({A} : Set (RealSquare d))) :
    realMatrixProduct w = A ^ w.length := by
  induction w with
  | nil => simp [realMatrixProduct]
  | cons B w ih =>
    have hB : B = A := hw B (by simp)
    have hh := ih (fun C hC => hw C (by simp [hC]))
    simpa [realMatrixProduct, hB, List.reverse_cons, List.prod_append, pow_succ] using
      congrArg (fun M => M * A) hh

theorem singleton_growth {d : ℕ} (A : RealSquare d) (k : ℕ) :
    realFamilyGrowth {A} k = realSpectralNorm (A ^ k) := by
  have hs : realWordNorms {A} k = {realSpectralNorm (A ^ k)} := by
    ext r
    constructor
    · rintro ⟨w, hk, hw, rfl⟩
      simp only [Set.mem_singleton_iff]
      rw [singleton_word_product A w hw, hk]
    · rintro rfl
      refine ⟨List.replicate k A, by simp, ?_, ?_⟩
      · intro B hB
        simpa using (List.mem_replicate.mp hB).2
      · simp [realMatrixProduct]
  simp [realFamilyGrowth, hs]

theorem singleton_radius_nonneg {d : ℕ} (A : RealSquare d) :
    0 ≤ realRadius {A} := by
  apply le_csInf
  · exact ⟨realRootGrowth {A} 1, 1, le_rfl, rfl⟩
  · rintro r ⟨k, hk, rfl⟩
    exact Real.rpow_nonneg (by rw [singleton_growth]; exact norm_nonneg _) _

theorem singleton_radius_le_root {d : ℕ} (A : RealSquare d) (k : ℕ) (hk : 1 ≤ k) :
    realRadius {A} ≤ realRootGrowth {A} k := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨j, hj, rfl⟩
    exact Real.rpow_nonneg (by rw [singleton_growth]; exact norm_nonneg _) _
  · exact ⟨k, hk, rfl⟩

theorem shift_radius_zero (n : ℕ) : realRadius {shift n} = 0 := by
  apply le_antisymm _ (singleton_radius_nonneg _)
  have h := singleton_radius_le_root (shift n) (n+1) (by omega)
  have hr : realRootGrowth {shift n} (n+1) = 0 := by
    rw [realRootGrowth, singleton_growth, shift_nilpotent]
    simp only [realSpectralNorm, map_zero, norm_zero]
    exact Real.zero_rpow (by positivity)
  rwa [hr] at h

theorem singleton_radius_ge_eigenvalue {d : ℕ} (A : RealSquare d) (r : ℝ) (hr : 0 ≤ r)
    (x : RealVector d) (hx : x ≠ 0)
    (he : Matrix.toEuclideanCLM (𝕜 := ℝ) A x = r • x) : r ≤ realRadius {A} := by
  have hp (k : ℕ) : Matrix.toEuclideanCLM (𝕜 := ℝ) (A^k) x = r^k • x := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ, map_mul, ContinuousLinearMap.mul_apply, he, map_smul, ih,
        smul_smul, mul_comm]
  have hnorm (k : ℕ) : r^k ≤ realSpectralNorm (A^k) := by
    have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) (A^k)).le_opNorm x
    rw [hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr k)] at h
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    change r^k ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A^k)‖
    nlinarith
  apply le_csInf
  · exact ⟨realRootGrowth {A} 1, 1, le_rfl, rfl⟩
  · rintro s ⟨k, hk, rfl⟩
    rw [realRootGrowth, singleton_growth]
    have h := Real.rpow_le_rpow (pow_nonneg hr k) (hnorm k) (by positivity : 0 ≤ 1/(k:ℝ))
    have heq : (r^k) ^ (1/(k:ℝ)) = r := by
      simpa only [one_div] using Real.pow_rpow_inv_natCast hr (by omega : k ≠ 0)
    rwa [heq] at h

theorem perturbation_radius_lower (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    r ≤ realRadius {perturbation n (r^(n+1))} :=
  singleton_radius_ge_eigenvalue _ r hr _ (eigenvector_ne_zero n r)
    (perturbation_eigenvector n r)

#print axioms shift_radius_zero
end NLA.MF05.Paper.Cyclic
