module

public import NLA.IV04.PaperCubeDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

def intervalBox (P : IntegerPartition) : RationalMatrixBox P.layerCount where
  lower := P.rationalLower
  upper := P.rationalUpper
  ordered := by
    intro i j
    by_cases h : i.val=j.val+1 ∧ i.val%4=2
    · have hne : i ≠ j := by intro he; subst j; omega
      have hu : j.val ≠ i.val+1 := by omega
      have h0 : i.val%4 ≠ 0 := by omega
      have h1 : i.val%4 ≠ 1 := by omega
      simp only [rationalUpper,if_pos h,rationalLower,if_neg hne,if_neg hu,
        if_pos h.1,if_neg h0,if_neg h1]
      norm_num
    · simp [rationalUpper,h]

def parametersOf (P : IntegerPartition) (A : Mat P.layerCount) (k : ℕ) : ℝ :=
  if h : k < P.m-1 then A (P.uncertainRow ⟨k,h⟩) (P.uncertainColumn ⟨k,h⟩) else 0

end IV04.Paper.IntegerPartition
