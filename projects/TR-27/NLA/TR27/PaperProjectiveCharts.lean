module

public import NLA.TR27.PaperProjectiveCompactness
public import NLA.TR27.PaperProjectiveChartDefinitions
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

theorem projectiveProjector_diagonal_ne_zero_iff {n : ℕ} (p : ℙ ℂ (Fin n → ℂ)) (i : Fin n) :
    projectiveProjector p i i ≠ 0 ↔ p.rep i ≠ 0 := by
  have hn : (coordinateNormSq p.rep : ℂ) ≠ 0 := by
    exact_mod_cast coordinateNormSq_ne_zero p.rep p.rep_nonzero
  simp [projectiveProjector, coordinateProjector, hn]

theorem projectiveCoordinateRatio_eq_projector {n : ℕ} (i j : Fin n) (p : ℙ ℂ (Fin n → ℂ)) :
    projectiveCoordinateRatio i j p = projectiveProjector p j i / projectiveProjector p i i := by
  by_cases hi : p.rep i = 0
  · simp [projectiveCoordinateRatio, projectiveProjector, coordinateProjector, hi]
  · exact (coordinateProjector_ratio p.rep p.rep_nonzero j i hi).symm

theorem projectiveCoordinateRatio_mk {n : ℕ} (i j : Fin n) (v : Fin n → ℂ) (hv : v ≠ 0) :
    projectiveCoordinateRatio i j (Projectivization.mk ℂ v hv) = v j / v i := by
  obtain ⟨c,hc,heq⟩ := represents_mk v hv
  rw [projectiveCoordinateRatio, heq]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

theorem projective_coordinate_domain_open {n : ℕ} (i : Fin n) :
    IsOpen {p : ℙ ℂ (Fin n → ℂ) | p.rep i ≠ 0} := by
  have h : Continuous (fun p : ℙ ℂ (Fin n → ℂ) => projectiveProjector p i i) :=
    ((continuous_apply i).comp ((continuous_apply i).comp (continuous_projectiveProjector n)))
  simpa only [projectiveProjector_diagonal_ne_zero_iff] using
    isOpen_ne_fun h (continuous_const : Continuous (fun _ : ℙ ℂ (Fin n → ℂ) => (0 : ℂ)))

theorem continuousAt_projectiveCoordinateRatio {n : ℕ} (i j : Fin n)
    (p : ℙ ℂ (Fin n → ℂ)) (hi : p.rep i ≠ 0) :
    ContinuousAt (projectiveCoordinateRatio i j) p := by
  have h (j k : Fin n) : Continuous (fun p : ℙ ℂ (Fin n → ℂ) => projectiveProjector p j k) :=
    ((continuous_apply k).comp ((continuous_apply j).comp (continuous_projectiveProjector n)))
  simp_rw [show projectiveCoordinateRatio i j =
    (fun q => projectiveProjector q j i / projectiveProjector q i i) from
      funext (projectiveCoordinateRatio_eq_projector i j)]
  exact (h j i).continuousAt.div (h i i).continuousAt
    ((projectiveProjector_diagonal_ne_zero_iff p i).mpr hi)

theorem continuous_projectiveChartInverse {n : ℕ} (i : Fin (n+1)) :
    Continuous (projectiveChartInverse i) := by
  have h : Continuous (fun v : Fin n → ℂ => (Fin.insertNth i (1 : ℂ) v : Fin (n+1) → ℂ)) :=
    continuous_const.finInsertNth i continuous_id
  exact (continuous_coordinate_projective_mk (n+1)).comp (h.subtype_mk _)

theorem projectiveChartInverse_mem {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℂ) :
    (projectiveChartInverse i v).rep i ≠ 0 := by
  obtain ⟨c,hc,heq⟩ := represents_mk (Fin.insertNth i (1 : ℂ) v : Fin (n+1) → ℂ)
    (show (Fin.insertNth i (1 : ℂ) v : Fin (n+1) → ℂ) ≠ 0 from by
      intro hz; have h := congrFun hz i; simpa using h)
  change (Projectivization.mk ℂ (Fin.insertNth i (1 : ℂ) v : Fin (n+1) → ℂ) _).rep i ≠ 0
  rw [heq]
  simpa [Pi.smul_apply, smul_eq_mul] using hc

theorem projectiveChart_right_inverse {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℂ) :
    (fun j => projectiveCoordinateRatio i (i.succAbove j) (projectiveChartInverse i v)) = v := by
  ext j
  simp [projectiveChartInverse, projectiveCoordinateRatio_mk]

theorem projectiveChart_left_inverse {n : ℕ} (i : Fin (n+1))
    (p : ℙ ℂ (Fin (n+1) → ℂ)) (hi : p.rep i ≠ 0) :
    projectiveChartInverse i (fun j => projectiveCoordinateRatio i (i.succAbove j) p) = p := by
  unfold projectiveChartInverse
  calc
    _ = Projectivization.mk ℂ p.rep p.rep_nonzero := by
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨(p.rep i)⁻¹, ?_⟩
      ext k
      by_cases hk : k = i
      · subst k
        simp [Pi.smul_apply, smul_eq_mul, hi]
      · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hk
        simp [Pi.smul_apply, smul_eq_mul, projectiveCoordinateRatio, div_eq_mul_inv, mul_comm]
    _ = p := p.mk_rep

/-- The ordinary affine chart obtained by setting coordinate i to one and
deleting it. Both topologies are fixed independently of the paper's curve. -/
def coordinateProjectiveChart {n : ℕ} (i : Fin (n+1)) :
    OpenPartialHomeomorph (ℙ ℂ (Fin (n+1) → ℂ)) (Fin n → ℂ) where
  toFun p j := projectiveCoordinateRatio i (i.succAbove j) p
  invFun := projectiveChartInverse i
  source := {p | p.rep i ≠ 0}
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun v _ => projectiveChartInverse_mem i v
  left_inv' := fun p hp => projectiveChart_left_inverse i p hp
  right_inv' := fun v _ => projectiveChart_right_inverse i v
  open_source := projective_coordinate_domain_open i
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro j
    exact continuousAt_projectiveCoordinateRatio i (i.succAbove j) p hp
  continuousOn_invFun := (continuous_projectiveChartInverse i).continuousOn

theorem coordinateProjectiveCharts_cover (n : ℕ) (p : ℙ ℂ (Fin (n+1) → ℂ)) :
    ∃ i, p ∈ (coordinateProjectiveChart i).source := by
  by_contra h
  push Not at h
  apply p.rep_nonzero
  ext i
  exact not_ne_iff.mp (h i)

#print axioms coordinateProjectiveChart
#print axioms coordinateProjectiveCharts_cover
end NLA.TR27.Paper
