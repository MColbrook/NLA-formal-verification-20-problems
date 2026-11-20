module

public import NLA.RA02.PaperPrefixCardinality
public import NLA.RA02.PaperSharpFamily
public import NLA.RA02.PaperCauchy

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem normalizedPrefix_outside {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n)
    (i : OutsideRow rows) (j : Fin s) :
    normalizedPrefix hs rows 0 i.val j =
      if Fin.castLE hs j ∉ Set.range rows then ((rows i.val).val+j.val+2 : ℝ)⁻¹ else 0 := by
  have hlt : Fin.castLE hs j < rows i.val := by
    change j.val < (rows i.val).val
    exact j.isLt.trans_le i.property
  have hne : rows i.val ≠ Fin.castLE hs j := Ne.symm hlt.ne
  simp [normalizedPrefix, hlt, lower_zero, Matrix.one_apply, hne]

theorem normalizedPrefix_zero_det_ne_zero {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    (normalizedPrefix hs rows 0).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hmissing : ∀ j : MissingColumn hs rows, v j.val = 0 := by
    let x : OutsideRow rows → ℝ := fun i => (rows i.val).val + 1
    let y : MissingColumn hs rows → ℝ := fun j => j.val.val + 1
    have hx : Function.Injective x := by
      intro a b h
      apply Subtype.ext
      apply rows.injective
      apply Fin.ext
      dsimp [x] at h
      exact_mod_cast (add_right_cancel h)
    have hy : Function.Injective y := by
      intro a b h
      apply Subtype.ext
      apply Fin.ext
      dsimp [y] at h
      exact_mod_cast (add_right_cancel h)
    have hxy (i : OutsideRow rows) (j : MissingColumn hs rows) : x i + y j ≠ 0 := by
      dsimp [x,y]
      positivity
    have hc := missingColumn_card_eq_outsideRow hs rows
    have hsum (i : OutsideRow rows) :
        ∑ j : MissingColumn hs rows, (x i + y j)⁻¹ * v j.val = 0 := by
      have hz := congrFun hzero i.val
      change (∑ j, normalizedPrefix hs rows 0 i.val j * v j) = 0 at hz
      simp only [normalizedPrefix_outside, ite_mul, zero_mul] at hz
      rw [← Finset.sum_filter] at hz
      rw [Finset.sum_subtype (p := fun j : Fin s => Fin.castLE hs j ∉ Set.range rows)
        _ (by simp)] at hz
      convert! hz using 1 <;> congr 1
      funext j
      dsimp [x,y]
      congr 2
      ring
    have he := cauchy_kernel_trivial x y hx hy hxy hc.le (fun j => v j.val) hsum
    intro j
    exact congrFun he j
  apply hv
  funext j
  change v j = 0
  by_cases hj : Fin.castLE hs j ∈ Set.range rows
  · obtain ⟨i, hi⟩ := hj
    have hz := congrFun hzero i
    change (∑ k, normalizedPrefix hs rows 0 i k * v k) = 0 at hz
    have ht (k : Fin s) : normalizedPrefix hs rows 0 i k * v k = if k = j then v j else 0 := by
      by_cases hk : Fin.castLE hs k ∈ Set.range rows
      · have he : rows i = Fin.castLE hs k ↔ j = k := by
          rw [hi]
          constructor
          · intro h
            have hh : j.val = k.val := congrArg (fun z : Fin n => z.val) h
            exact Fin.ext hh
          · rintro rfl; rfl
        simp only [normalizedPrefix, not_not, hk, not_true_eq_false, if_false,
          lower_zero, Matrix.one_apply, he]
        by_cases hkj : k = j
        · subst k; simp
        · simp [hkj, Ne.symm hkj]
      · have hvk := hmissing ⟨k,hk⟩
        have hkj : k ≠ j := by
          intro h
          subst k
          exact hk ⟨i,hi⟩
        simp [hvk,hkj]
    simpa only [ht, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hz
  · exact hmissing ⟨j,hj⟩

#print axioms normalizedPrefix_zero_det_ne_zero
end NLA.RA02.Paper
