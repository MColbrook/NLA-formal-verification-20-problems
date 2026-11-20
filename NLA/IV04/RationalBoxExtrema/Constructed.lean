module

public import NLA.IV04.RationalBoxExtrema.RegularBox
public import NLA.IV04.PaperConstructedHull

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reference.IV04RationalBoxExtrema
open Reference.IV04AffinePolyhedronSteps

def rationalCornerRhs (n : ℕ) (hn : 0 < n) : Fin n → ℚ :=
  Pi.single ⟨n-1,Nat.sub_lt hn (by decide)⟩ (-1)

theorem rational_corner_cast (n : ℕ) (hn : 0 < n) :
    realVector (rationalCornerRhs n hn) = IV04.Paper.positiveCornerRhs n hn := by
  classical
  ext i
  simp [realVector,rationalCornerRhs,IV04.Paper.positiveCornerRhs,Pi.single_apply]
  split_ifs <;> norm_num

theorem regular_positive_box_coordinate_extrema {n : ℕ} (hn : 0 < n)
    (B : IV04.Paper.RationalMatrixBox n)
    (hd : ∀ A ∈ B.realizations, A.det ≠ 0) (j : Fin n) :
    ∃ qlo qhi : Fin n → ℚ,
      realVector qlo ∈ IV04.Paper.positiveSolutions n hn B.realizations ∧
      realVector qhi ∈ IV04.Paper.positiveSolutions n hn B.realizations ∧
      ∀ x ∈ IV04.Paper.positiveSolutions n hn B.realizations,
        (qlo j : ℝ) ≤ x j ∧ x j ≤ (qhi j : ℝ) := by
  have heq : solutions B.lower B.upper (rationalCornerRhs n hn) =
      IV04.Paper.positiveSolutions n hn B.realizations := by
    ext x
    change (∃ A ∈ B.realizations, A *ᵥ x = realVector (rationalCornerRhs n hn)) ↔ _
    rw [rational_corner_cast]
    rfl
  simpa only [heq] using regular_box_rational_coordinate_extrema B
    (rationalCornerRhs n hn) hd j

theorem constructed_all_coordinate_rational_extrema (P : IV04.Paper.IntegerPartition)
    (j : Fin P.layerCount) :
    ∃ qlo qhi : Fin P.layerCount → ℚ, realVector qlo ∈ P.constructedSolutions ∧
      realVector qhi ∈ P.constructedSolutions ∧
      ∀ x ∈ P.constructedSolutions, (qlo j : ℝ) ≤ x j ∧ x j ≤ (qhi j : ℝ) := by
  exact regular_positive_box_coordinate_extrema P.layerCount_pos P.intervalBox
    (fun A hA => ne_of_gt (P.intervalBox_regular A hA)) j

theorem regular_positive_box_endpoint_functions {n : ℕ} (hn : 0 < n)
    (B : IV04.Paper.RationalMatrixBox n)
    (hd : ∀ A ∈ B.realizations, A.det ≠ 0) :
    ∃ lo hi : Fin n → ℚ, ∀ j : Fin n,
      IsLeast ((fun x : Fin n → ℝ => x j) ''
        IV04.Paper.positiveSolutions n hn B.realizations) (lo j : ℝ) ∧
      IsGreatest ((fun x : Fin n → ℝ => x j) ''
        IV04.Paper.positiveSolutions n hn B.realizations) (hi j : ℝ) := by
  classical
  choose qlo qhi hlo hhi hbounds using regular_positive_box_coordinate_extrema hn B hd
  refine ⟨fun j => qlo j j,fun j => qhi j j,?_⟩
  intro j
  constructor
  · refine ⟨⟨realVector (qlo j),hlo j,rfl⟩,?_⟩
    rintro z ⟨x,hx,rfl⟩
    exact (hbounds j x hx).1
  · refine ⟨⟨realVector (qhi j),hhi j,rfl⟩,?_⟩
    rintro z ⟨x,hx,rfl⟩
    exact (hbounds j x hx).2

#print axioms rational_corner_cast
#print axioms regular_positive_box_coordinate_extrema
#print axioms constructed_all_coordinate_rational_extrema
#print axioms regular_positive_box_endpoint_functions
end Reference.IV04RationalBoxExtrema
