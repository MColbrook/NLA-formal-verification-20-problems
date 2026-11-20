module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- Bounded integer numerator/common-denominator certificates from original pointed inequalities. -/
public import NLA.IV04.PolyhedronSupportReplayR3.AffinePolyhedronSteps.IntegerCertificate

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

theorem exists_bounded_integer_extreme_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (H : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (hne : ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x)
    (hline : lineFree (integerRealMatrix A) (integerRealVector b)) :
    ∃ x : Fin n → ℝ,
      x ∈ (feasibleSet (integerRealMatrix A) (integerRealVector b)).extremePoints ℝ ∧
      ∃ p : Fin n → ℤ, ∃ d : ℤ,
        d ≠ 0 ∧ |d| ≤ (gramCertificateBound (Fintype.card ι) n H : ℤ) ∧
        (∀ j, |p j| ≤ (gramCertificateBound (Fintype.card ι) n H : ℤ)) ∧
        ∀ j, x j=(p j : ℝ)/(d : ℝ) := by
  classical
  obtain ⟨x,hx,hkernel⟩ := exists_extreme_point_of_lineFree
    (integerRealMatrix A) (integerRealVector b) hne hline
  let M : Matrix ι (Fin n) ℤ := fun i j =>
    if i ∈ tightRows (integerRealMatrix A) (integerRealVector b) x then A i j else 0
  let c : ι → ℤ := fun i =>
    if i ∈ tightRows (integerRealMatrix A) (integerRealVector b) x then b i else 0
  have hsys : integerRealMatrix M *ᵥ x=integerRealVector c := by
    funext i
    change (∑ j, ((if i ∈ tightRows (integerRealMatrix A) (integerRealVector b) x
      then A i j else 0 : ℤ) : ℝ)*x j)=
      ((if i ∈ tightRows (integerRealMatrix A) (integerRealVector b) x then b i else 0 : ℤ) : ℝ)
    by_cases hi : i ∈ tightRows (integerRealMatrix A) (integerRealVector b) x
    · simp only [if_pos hi]
      exact (mem_tightRows (integerRealMatrix A) (integerRealVector b) x i).mp hi
    · simp only [if_neg hi,Int.cast_zero,zero_mul,Finset.sum_const_zero]
  have hker : ∀ d : Fin n → ℝ, integerRealMatrix M *ᵥ d=0 → d=0 := by
    intro d hd
    apply hkernel d
    intro i hi
    have he := congrFun hd i
    change (∑ j, ((if i ∈ tightRows (integerRealMatrix A) (integerRealVector b) x
      then A i j else 0 : ℤ) : ℝ)*d j)=0 at he
    simp only [if_pos hi] at he
    exact he
  have hM : ∀ i j, |M i j| ≤ (H : ℤ) := by
    intro i j
    dsimp [M]
    split_ifs
    · exact hA i j
    · simp
  have hc : ∀ i, |c i| ≤ (H : ℤ) := by
    intro i
    dsimp [c]
    split_ifs
    · exact hb i
    · simp
  exact ⟨x,hx,integer_full_system_certificate M c x H hsys hker hM hc⟩

#print axioms exists_bounded_integer_extreme_certificate
end
end Reference.IV04AffinePolyhedronSteps
