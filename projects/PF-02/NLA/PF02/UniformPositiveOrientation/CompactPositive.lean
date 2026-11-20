module

public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Compactness.Compact

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Set Filter
open scoped Topology

theorem compact_parameter_positive {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (K : Set (ℝ × X)) (L : Set Y) (hK : IsCompact K) (hL : IsCompact L)
    (g : X × Y → ℝ) (hg : Continuous g)
    (hzero : ∀ x : X, (0,x) ∈ K → ∀ y : Y, y ∈ L → 0 < g (x,y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∀ x : X, (t,x) ∈ K → ∀ y : Y, y ∈ L → 0 < g (x,y) := by
  classical
  let D : Set ((ℝ × X) × Y) := K ×ˢ L
  have hD : IsCompact D := hK.prod hL
  let psi : ((ℝ × X) × Y) → ℝ := fun Z => g (Z.1.2,Z.2)
  have hc : Continuous psi := hg.comp (continuous_fst.snd.prodMk continuous_snd)
  let bad : Set ((ℝ × X) × Y) := D ∩ {Z | psi Z ≤ 0}
  have hb : IsCompact bad := hD.inter_right (isClosed_le hc continuous_const)
  let E : Set ℝ := (fun Z : ((ℝ × X) × Y) => Z.1.1) '' bad
  have hE : IsCompact E := hb.image (continuous_fst.fst)
  have hn : (0 : ℝ) ∉ E := by
    rintro ⟨Z,⟨hdom,hbad⟩,he⟩
    have hpair : Z.1 = (0,Z.1.2) := Prod.ext he rfl
    have hpoint : (0,Z.1.2) ∈ K := hpair ▸ hdom.1
    exact (not_le_of_gt (hzero Z.1.2 hpoint Z.2 hdom.2)) hbad
  have hnh : Eᶜ ∈ 𝓝 (0 : ℝ) := hE.isClosed.isOpen_compl.mem_nhds hn
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnh
  refine ⟨ε,hε,?_⟩
  intro t ht x hx y hy
  by_contra hbad
  have htE : t ∈ E := ⟨((t,x),y),⟨⟨hx,hy⟩,le_of_not_gt hbad⟩,rfl⟩
  have htball : t ∈ Metric.ball 0 ε := by simpa [Metric.mem_ball,Real.dist_eq] using ht
  exact (hball htball) htE

#print axioms compact_parameter_positive
end Reference.PF02UniformPositiveOrientation
