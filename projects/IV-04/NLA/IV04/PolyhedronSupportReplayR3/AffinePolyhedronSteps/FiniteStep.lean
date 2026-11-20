module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- The actual minimum positive slack ratio gives a feasible step and a new tight row. -/
public import NLA.IV04.PolyhedronSupportReplayR3.AffinePolyhedronSteps.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 theorem finite_boundary_step {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x d : Fin n → ℝ)
    (hx : feasible A b x)
    (hT : ∀ i ∈ tightRows A b x, (A *ᵥ d) i=0)
    (hpositive : ∃ i, 0 < (A *ᵥ d) i) :
    ∃ t : ℝ, 0 < t ∧ feasible A b (x+t • d) ∧
      tightRows A b x ⊂ tightRows A b (x+t • d) := by
  classical
  let positiveRows : Finset ι := Finset.univ.filter (fun i => 0 < (A *ᵥ d) i)
  have hnonempty : positiveRows.Nonempty := by
    obtain ⟨i,hi⟩ := hpositive
    exact ⟨i,by simp [positiveRows,hi]⟩
  let ratio : ι → ℝ := fun i => (b i-(A *ᵥ x) i)/(A *ᵥ d) i
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image positiveRows ratio hnonempty
  have hjpos : 0 < (A *ᵥ d) j := (Finset.mem_filter.mp hj).2
  have hjnot : j ∉ tightRows A b x := by
    intro ht
    have hz := hT j ht
    linarith
  have hjstrict : (A *ᵥ x) j < b j := by
    rcases lt_or_eq_of_le (hx j) with hlt | heq
    · exact hlt
    · exact False.elim (hjnot ((mem_tightRows A b x j).mpr heq))
  have htpos : 0 < ratio j := div_pos (sub_pos.mpr hjstrict) hjpos
  have hy : feasible A b (x+ratio j • d) := by
    intro i
    rw [mulVec_shift]
    by_cases hipos : 0 < (A *ᵥ d) i
    · have himem : i ∈ positiveRows := by simp [positiveRows,hipos]
      have hbound := hmin i himem
      change ratio j ≤ (b i-(A *ᵥ x) i)/(A *ᵥ d) i at hbound
      have hm := (le_div_iff₀ hipos).mp hbound
      linarith
    · have hinonpos : (A *ᵥ d) i ≤ 0 := le_of_not_gt hipos
      have hm : ratio j*(A *ᵥ d) i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hinonpos
      have hh := hx i
      linarith
  have hsubset : tightRows A b x ⊆ tightRows A b (x+ratio j • d) := by
    intro i hi
    apply (mem_tightRows A b _ i).mpr
    rw [mulVec_shift, hT i hi, mul_zero, add_zero]
    exact (mem_tightRows A b x i).mp hi
  have hjnew : j ∈ tightRows A b (x+ratio j • d) := by
    apply (mem_tightRows A b _ j).mpr
    rw [mulVec_shift]
    dsimp [ratio]
    rw [div_mul_cancel₀ _ hjpos.ne']
    ring
  refine ⟨ratio j,htpos,hy,Finset.ssubset_iff_subset_ne.mpr ⟨hsubset,?_⟩⟩
  intro heq
  exact hjnot (heq.symm ▸ hjnew)

#print axioms finite_boundary_step
end
end Reference.IV04AffinePolyhedronSteps
