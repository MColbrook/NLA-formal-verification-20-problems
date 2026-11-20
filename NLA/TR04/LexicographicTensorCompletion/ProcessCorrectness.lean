module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Genuine arbitrary-order finite tensor TT approximation by recursive optimal projections.
All cuts are actual grouped/reindexed matrix ranks; the error induction uses exact Pythagoras.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.LexicographicTensorCompletion.CanonicalFrame

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage

theorem ttSVD_correct {m : ℕ} {ns : List ℕ}
    (A : Tensor m ns) (rs : List ℕ) (hlen : rs.length=ns.length) :
    feasible m ns (ttSVD m ns A rs) rs ∧
      ∀ Y : Tensor m ns, feasible m ns Y rs →
        tensorFrobeniusSq (A-ttSVD m ns A rs) ≤ (ns.length : ℝ)*tensorFrobeniusSq (A-Y) := by
  classical
  induction ns generalizing m rs with
  | nil =>
    have hrs : rs=[] := by simpa using hlen
    subst rs
    refine ⟨by simp only [ttSVD,feasible], ?_⟩
    intro Y hY
    simp [ttSVD,tensorFrobeniusSq]
  | cons n ns ih =>
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      have hlen' : rs.length=ns.length := by simpa using hlen
      let U := svdFrame A r
      have hPrimitive := svdFrame_correct A r
      have hU := hPrimitive.1
      have hOptimal := hPrimitive.2
      let C : Tensor (min r m) (n::ns) := U.transpose*A
      let Z := ttSVD (rowCount (min r m) n) ns (merge C) rs
      have hRec := ih (merge C) rs hlen'
      have hZ := hRec.1
      have hApprox := hRec.2
      let C' : Tensor (min r m) (n::ns) := unmerge (m:=min r m) (n:=n) Z
      let X := U*C'
      have hMerge : merge C'=Z := merge_unmerge Z
      have hFirst : X.rank ≤ r :=
        (Matrix.rank_mul_le_left U C').trans ((Matrix.rank_le_width U).trans (Nat.min_le_left r m))
      have hFeasible : feasible m (n::ns) X (r::rs) := by
        simp only [feasible]
        refine ⟨hFirst,?_⟩
        change feasible (rowCount m n) ns (merge (U*C')) rs
        rw [merge_mul, hMerge]
        exact feasible_mul (mergeLeft U) Z rs hZ
      simp only [ttSVD]
      change feasible m (n::ns) X (r::rs) ∧ _
      refine ⟨hFeasible,?_⟩
      intro Y hY
      have hY' := hY
      simp only [feasible] at hY'
      have hCompressed := feasible_merge_of_cons (U.transpose*Y) r rs
        (feasible_mul U.transpose Y (r::rs) hY)
      have h := hApprox (merge (U.transpose*Y)) hCompressed
      have hLeft : tensorFrobeniusSq (merge C-Z) = tensorFrobeniusSq (C-C') := by
        rw [← hMerge, ← merge_sub, merge_frobeniusSq]
      have hRight : tensorFrobeniusSq (merge C-merge (U.transpose*Y)) =
          tensorFrobeniusSq (U.transpose*(A-Y)) := by
        rw [← merge_sub]
        have hsub : C-U.transpose*Y = U.transpose*(A-Y) := by
          dsimp [C]
          rw [Matrix.mul_sub]
        rw [hsub, merge_frobeniusSq]
      rw [hLeft,hRight] at h
      have hCompression := tensor_compression_frobenius_le U hU (A-Y)
      have hWeighted := mul_le_mul_of_nonneg_left hCompression
        (show (0:ℝ) ≤ (ns.length : ℝ) by exact Nat.cast_nonneg _)
      have hProjection := hOptimal Y hY'.1
      have hError := tensor_column_error_decomposition U hU A C'
      calc
        tensorFrobeniusSq (A-X) = tensorFrobeniusSq (A-U*U.transpose*A) +
            tensorFrobeniusSq (C-C') := hError
        _ ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
            (ns.length : ℝ)*tensorFrobeniusSq (U.transpose*(A-Y)) := add_le_add le_rfl h
        _ ≤ tensorFrobeniusSq (A-Y) + (ns.length : ℝ)*tensorFrobeniusSq (A-Y) :=
          add_le_add hProjection hWeighted
        _ = ((n::ns).length : ℝ)*tensorFrobeniusSq (A-Y) := by
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
          ring

#print axioms ttSVD_correct

theorem completeFrame_correct {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (hU : U.transpose*U=1)
    (r1 : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hk : k ≤ r1) :
    feasible m (n::ns) (completeFrame A U rs) (r1::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r1::rs) →
        tensorFrobeniusSq (A-completeFrame A U rs) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
          (ns.length : ℝ)*tensorFrobeniusSq (U.transpose*(A-Y)) ∧
        tensorFrobeniusSq (A-completeFrame A U rs) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
          (ns.length : ℝ)*tensorFrobeniusSq (U*U.transpose*(A-Y)) := by
  classical
  let C : Tensor k (n::ns) := U.transpose*A
  let Z := ttSVD (rowCount k n) ns (merge C) rs
  have hRec := ttSVD_correct (merge C) rs hlen
  have hZ := hRec.1
  have hApprox := hRec.2
  let C' : Tensor k (n::ns) := unmerge (m:=k) (n:=n) Z
  let X := U*C'
  have hMerge : merge C'=Z := merge_unmerge Z
  have hFirst : X.rank ≤ r1 :=
    (Matrix.rank_mul_le_left U C').trans ((Matrix.rank_le_width U).trans hk)
  have hFeasible : feasible m (n::ns) X (r1::rs) := by
    simp only [feasible]
    refine ⟨hFirst,?_⟩
    change feasible (rowCount m n) ns (merge (U*C')) rs
    rw [merge_mul,hMerge]
    exact feasible_mul (mergeLeft U) Z rs hZ
  change feasible m (n::ns) X (r1::rs) ∧ _
  refine ⟨hFeasible,?_⟩
  intro Y hY
  have hCompressed := feasible_merge_of_cons (U.transpose*Y) r1 rs
    (feasible_mul U.transpose Y (r1::rs) hY)
  have h := hApprox (merge (U.transpose*Y)) hCompressed
  have hLeft : tensorFrobeniusSq (merge C-Z) = tensorFrobeniusSq (C-C') := by
    rw [← hMerge, ← merge_sub, merge_frobeniusSq]
  have hRight : tensorFrobeniusSq (merge C-merge (U.transpose*Y)) =
      tensorFrobeniusSq (U.transpose*(A-Y)) := by
    rw [← merge_sub]
    have hsub : C-U.transpose*Y = U.transpose*(A-Y) := by
      dsimp [C]
      rw [Matrix.mul_sub]
    rw [hsub,merge_frobeniusSq]
  rw [hLeft,hRight] at h
  have hError := tensor_column_error_decomposition U hU A C'
  have hBound : tensorFrobeniusSq (A-X) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
      (ns.length : ℝ)*tensorFrobeniusSq (U.transpose*(A-Y)) := by
    change tensorFrobeniusSq (A-U*C') ≤ _
    rw [hError]
    exact add_le_add le_rfl h
  have hnorm := tensor_lifting_frobenius_eq U hU (U.transpose*(A-Y))
  have hnorm' : tensorFrobeniusSq (U*U.transpose*(A-Y)) =
      tensorFrobeniusSq (U.transpose*(A-Y)) := by
    simpa only [Matrix.mul_assoc] using hnorm
  exact ⟨hBound,by rw [hnorm']; exact hBound⟩

#print axioms completeFrame_correct
end
end Reference.LexTensorCompletion
