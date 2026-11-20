module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
The genuine feasible minimum is attained; the fixed solver uses no optimizer input. -/
public import NLA.TR04.TensorOptimumAttainment.Attainment

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.TensorOptimumAttainment
noncomputable section
open Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection

theorem actual_optimal_error_attained {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) (hlen : rs.length=ns.length) :
    ∃ B : Tensor m ns, feasible m ns B rs ∧ error A B=optimalError A rs ∧
      ∀ Y : Tensor m ns, feasible m ns Y rs → error A B≤error A Y := by
  obtain ⟨B,hB,hmin⟩ := actual_best_feasible_tensor_exists A rs hlen
  have hleast : IsLeast (error A '' feasibleSet m ns rs) (error A B) := by
    refine ⟨⟨B,hB,rfl⟩,?_⟩
    rintro e ⟨Y,hY,rfl⟩
    exact hmin Y hY
  exact ⟨B,hB,hleast.csInf_eq.symm,hmin⟩

theorem actual_optimal_error_nonneg {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) (hlen : rs.length=ns.length) : 0≤optimalError A rs := by
  obtain ⟨B,_,hE,_⟩ := actual_optimal_error_attained A rs hlen
  rw [← hE]
  exact tensorFrobeniusSq_nonneg _

theorem actual_optimal_error_zero_iff_feasible {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) (hlen : rs.length=ns.length) :
    optimalError A rs=0 ↔ feasible m ns A rs := by
  obtain ⟨B,hB,hE,hmin⟩ := actual_optimal_error_attained A rs hlen
  constructor
  · intro hz
    have hZ : Reference.RecursiveTensorCompletion.denseTensor (A-B)=0 :=
      (Reference.RealOptimalityEquality.frobeniusSq_eq_zero_iff _).mp (by
        rw [Reference.CyclicBoundary.denseTensor_frobenius]
        exact hE.trans hz)
    have h := congrArg (fun M => M.submatrix id (Fintype.equivFin (ModeIndex ns))) hZ
    have hAB : A-B=0 := by simpa [Reference.RecursiveTensorCompletion.denseTensor,Matrix.submatrix_submatrix] using h
    have he : A=B := sub_eq_zero.mp hAB
    exact he.symm ▸ hB
  · intro hA
    have h := hmin A hA
    have hn := actual_optimal_error_nonneg A rs hlen
    rw [hE] at h
    have hz : error A A=0 := by simp [error,tensorFrobeniusSq]
    rw [hz] at h
    exact le_antisymm h hn

theorem actual_solver_with_genuine_feasible_minimum {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 0<m) :
    feasible m (n::ns) (solver A r rs) (r::rs) ∧ (candidates A r rs).length≤m ∧
      (0<optimalError A (r::rs) → error A (solver A r rs)<((ns.length : ℝ)+1)*optimalError A (r::rs)) ∧
      (optimalError A (r::rs)=0 → solver A r rs=A) := by
  obtain ⟨B,hB,hE,_⟩ := actual_optimal_error_attained A (r::rs) (by simpa using hlen)
  have h := actual_solver_mathematical_guarantee A r rs hlen hr hns hm
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro hp
    have hpB : 0<error A B := by rw [hE];exact hp
    simpa only [hE] using h.2.2.1 B hB hpB
  · intro hz
    exact h.2.2.2 B hB (hE.trans hz)

#print axioms actual_optimal_error_attained
#print axioms actual_optimal_error_nonneg
#print axioms actual_optimal_error_zero_iff_feasible
#print axioms actual_solver_with_genuine_feasible_minimum
end
end Reference.TensorOptimumAttainment
