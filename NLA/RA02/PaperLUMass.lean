module

public import NLA.RA02.PaperLUMassDefinitions
public import NLA.RA02.PaperLUHistoryResidual

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem luMass_as_list {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin k → Option (Fin n × Fin n)) :
    NLA.RA03.historyMass (complexify A) h = luListMass A (List.ofFn h) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
    rw [NLA.RA03.historyMass, complexify_lu_next, List.ofFn_succ, luListMass, ih]

theorem luListMass_append {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u w : List (Option (Fin n × Fin n))) :
    luListMass A (u++w) = luListMass A u * luListMass (realLUListPath A u) w := by
  induction u generalizing A with
  | nil => simp [luListMass, realLUListPath]
  | cons p u ih => simp only [List.cons_append, luListMass, realLUListPath, ih, mul_assoc]

theorem luNormalizerProduct_prefixes {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (w : List (Option (Fin n × Fin n))) :
    luNormalizerProduct A w = ∏ s : Fin w.length,
      NLA.RA03.frobeniusSq (complexify (realLUListPath A (w.take s.val))) := by
  induction w generalizing A with
  | nil => simp [luNormalizerProduct]
  | cons p w ih =>
    rw [luNormalizerProduct, ih]
    let f : Fin (w.length+1) → ℝ := fun s =>
      NLA.RA03.frobeniusSq (complexify (realLUListPath A ((p::w).take s.val)))
    change f 0 * (∏ s : Fin w.length, f s.succ) = ∏ s : Fin (w.length+1), f s
    exact (Fin.prod_univ_succ f).symm

theorem luNormalizerProduct_append {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u w : List (Option (Fin n × Fin n))) :
    luNormalizerProduct A (u++w) =
      luNormalizerProduct A u * luNormalizerProduct (realLUListPath A u) w := by
  induction u generalizing A with
  | nil => simp [luNormalizerProduct, realLUListPath]
  | cons p u ih => simp only [List.cons_append, luNormalizerProduct, realLUListPath, ih, mul_assoc]

theorem frobenius_nonzero_of_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hij : A i j ≠ 0) : NLA.RA03.frobeniusSq (complexify A) ≠ 0 := by
  rw [complexify_frobenius]
  have h1 : (A i j)^2 ≤ ∑ b, (A i b)^2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (A i b)) (Finset.mem_univ j)
  have h2 : (∑ b, (A i b)^2) ≤ ∑ a, ∑ b, (A a b)^2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (A a b))) (Finset.mem_univ i)
  exact ne_of_gt (lt_of_lt_of_le (sq_pos_of_ne_zero hij) (h1.trans h2))

theorem luMass_det {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    luNormalizerProduct A (List.ofFn (fun i => some (rows i,cols i))) ≠ 0 ∧
    luListMass A (List.ofFn (fun i => some (rows i,cols i))) =
      (A.submatrix rows cols).det^2 / luNormalizerProduct A (List.ofFn (fun i => some (rows i,cols i))) := by
  induction k with
  | zero => simp [List.ofFn_zero, luNormalizerProduct, luListMass, Matrix.det_isEmpty]
  | succ k ih =>
    let gr := historyPrefix rows (Nat.le_succ k)
    let gc := historyPrefix cols (Nat.le_succ k)
    have hg : k ≤ n := by omega
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k hg gr gc))
    have hb := residual_bordered_determinant A gr gc (rows (Fin.last k)) (cols (Fin.last k))
      (history_last_not_in_prefix rows) (history_last_not_in_prefix cols) hu
    simp only [gr, gc, history_append_prefix] at hb
    have he : interpolatoryResidual A gr gc (rows (Fin.last k)) (cols (Fin.last k)) ≠ 0 := by
      have hn := hA (k+1) hk rows cols
      rw [hb] at hn
      exact (mul_ne_zero_iff.mp hn).2
    have hR : interpolatoryResidual A gr gc ≠ 0 := by
      intro hh
      apply he
      rw [hh]
      rfl
    have hf := frobenius_nonzero_of_entry _ _ _ he
    obtain ⟨hprod,hmass⟩ := ih hg gr gc
    rw [List.ofFn_succ', List.concat_eq_append, luNormalizerProduct_append, luListMass_append]
    simp only [luNormalizerProduct, luListMass, mul_one]
    change luNormalizerProduct A (List.ofFn (fun i => some (gr i,gc i))) *
      NLA.RA03.frobeniusSq (complexify (realLUListPath A (List.ofFn (fun i => some (gr i,gc i))))) ≠ 0 ∧
      luListMass A (List.ofFn (fun i => some (gr i,gc i))) *
        NLA.RA03.pivotMass (complexify (realLUListPath A (List.ofFn (fun i => some (gr i,gc i)))))
        (some (rows (Fin.last k),cols (Fin.last k))) =
      (A.submatrix rows cols).det^2 /
        (luNormalizerProduct A (List.ofFn (fun i => some (gr i,gc i))) *
          NLA.RA03.frobeniusSq (complexify (realLUListPath A (List.ofFn (fun i => some (gr i,gc i))))))
    rw [realLUPath_distinct A hA hg gr gc]
    constructor
    · exact mul_ne_zero hprod hf
    · rw [hmass, complexify_joint_pivot_mass _ hR, ← complexify_frobenius, hb]
      field_simp
      <;> ring

theorem actual_luMass_det {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    NLA.RA03.historyMass (complexify A) (fun i => some (rows i,cols i)) =
      (A.submatrix rows cols).det^2 / luNormalizerProduct A (List.ofFn (fun i => some (rows i,cols i))) := by
  rw [luMass_as_list]
  exact (luMass_det A hA hk rows cols).2

#print axioms actual_luMass_det
end NLA.RA02.Paper
