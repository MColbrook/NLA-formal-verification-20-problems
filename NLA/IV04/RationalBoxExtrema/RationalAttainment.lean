module

public import NLA.IV04.RationalBoxExtrema.SignedPolyhedron
public import NLA.IV04.OriginalObjectiveAttainment.Attainment
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reference.IV04RationalBoxExtrema
open Reference.IV04AffinePolyhedronSteps

theorem compact_solutions_rational_objective_max {m n : ℕ}
    (L U : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hLU : ∀ i j, L i j ≤ U i j)
    (hne : (solutions L U b).Nonempty) (hc : IsCompact (solutions L U b))
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    ∃ q : Fin n → ℚ, realVector q ∈ solutions L U b ∧
      ∀ x ∈ solutions L U b, ℓ x ≤ ℓ (realVector q) := by
  classical
  obtain ⟨x,hx,hmax⟩ := hc.exists_isMaxOn hne
    ℓ.continuous_of_finiteDimensional.continuousOn
  obtain ⟨s,hs⟩ := (solutions_iff_actual_signed_polyhedron L U b hLU x).mp hx
  have hsubset : ∀ z, feasible (realMatrix (signedMatrix L U s))
      (realVector (signedBounds (n:=n) b)) z → z ∈ solutions L U b := by
    intro z hz
    exact (solutions_iff_actual_signed_polyhedron L U b hLU z).mpr ⟨s,hz⟩
  obtain ⟨q,hq,_,hqmax⟩ :=
    Reference.IV04OriginalObjectiveAttainment.rational_original_extreme_objective_attained
      (signedMatrix L U s) (signedBounds (n:=n) b) ℓ (ℓ x) ⟨x,hs⟩
      (signed_polyhedron_lineFree L U b s)
      (fun z hz => hmax (hsubset z hz))
  have hqfeas := ((mem_extremePoints_iff_left).mp hq).1
  refine ⟨q,hsubset _ hqfeas,?_⟩
  intro z hz
  exact (hmax hz).trans (hqmax x hs)

theorem compact_solutions_rational_coordinate_extrema {m n : ℕ}
    (L U : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hLU : ∀ i j, L i j ≤ U i j)
    (hne : (solutions L U b).Nonempty) (hc : IsCompact (solutions L U b))
    (j : Fin n) :
    ∃ qlo qhi : Fin n → ℚ, realVector qlo ∈ solutions L U b ∧
      realVector qhi ∈ solutions L U b ∧
      ∀ x ∈ solutions L U b, (qlo j : ℝ) ≤ x j ∧ x j ≤ (qhi j : ℝ) := by
  obtain ⟨qhi,hhi,hmax⟩ := compact_solutions_rational_objective_max L U b hLU hne hc
    (LinearMap.proj j)
  obtain ⟨qlo,hlo,hmin⟩ := compact_solutions_rational_objective_max L U b hLU hne hc
    (-(LinearMap.proj j))
  refine ⟨qlo,qhi,hlo,hhi,?_⟩
  intro x hx
  have h1 := hmin x hx
  have h2 := hmax x hx
  change -x j ≤ -(qlo j : ℝ) at h1
  change x j ≤ (qhi j : ℝ) at h2
  exact ⟨by linarith,h2⟩

#print axioms compact_solutions_rational_objective_max
#print axioms compact_solutions_rational_coordinate_extrema
end Reference.IV04RationalBoxExtrema
