module

public import NLA.RA08.RangeBasis.Definitions
public import NLA.RA08.RangeBasis.ChangeBasis
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
namespace NLA.RA08.Paper.RangeBasis

theorem same_range_change_of_basis {n l : ℕ} (Ω Q : Matrix (Fin n) (Fin l) ℝ)
    (hΩ : FullColumns Ω) (hQ : FullColumns Q) (hr : SameRange Ω Q) :
    ∃ T : Matrix (Fin l) (Fin l) ℝ, IsUnit T.det ∧ Ω * T = Q := by
  let f := Matrix.toLin' Ω
  let g := Matrix.toLin' Q
  have hf : Function.Injective f := hΩ
  have hg : Function.Injective g := hQ
  let ef := LinearEquiv.ofInjective f hf
  let eg := LinearEquiv.ofInjective g hg
  have hfg : LinearMap.range f = LinearMap.range g := hr
  let er : LinearMap.range g ≃ₗ[ℝ] LinearMap.range f := {
    toFun := fun x => ⟨x.val, by rw [hfg]; exact x.property⟩
    invFun := fun x => ⟨x.val, by rw [← hfg]; exact x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }
  let e := eg.trans (er.trans ef.symm)
  have he (x : Fin l → ℝ) : f (e x) = g x := by
    change f (ef.symm (er (eg x))) = g x
    exact (LinearEquiv.ofInjective_symm_apply f (h := hf) (er (eg x))).trans rfl
  let T := LinearMap.toMatrix' e.toLinearMap
  let U := LinearMap.toMatrix' e.symm.toLinearMap
  have hTU : T * U = 1 := by
    apply Matrix.toLin'.injective
    ext x i
    simp [T, U, Matrix.toLin'_mul]
  have hUT : U * T = 1 := by
    apply Matrix.toLin'.injective
    ext x i
    simp [T, U, Matrix.toLin'_mul]
  have hT : IsUnit T := ⟨⟨T, U, hTU, hUT⟩, rfl⟩
  refine ⟨T, T.isUnit_iff_isUnit_det.mp hT, ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_mul, LinearMap.comp_apply, T, Matrix.toLin'_toMatrix']
  exact he x

theorem nystrom_same_range {n l : ℕ} (A : RealMatrix n)
    (Ω Q : Matrix (Fin n) (Fin l) ℝ)
    (hΩ : FullColumns Ω) (hQ : FullColumns Q) (hr : SameRange Ω Q) :
    nystrom A Q = nystrom A Ω := by
  obtain ⟨T, hT, hQT⟩ := same_range_change_of_basis Ω Q hΩ hQ hr
  rw [← hQT]
  exact nystrom_basis_change A Ω T hT

theorem fullColumns_of_orthonormal {n l : ℕ} (Q : Matrix (Fin n) (Fin l) ℝ)
    (hQ : Q.transpose * Q = 1) : FullColumns Q := by
  intro x y h
  have ht := congrArg (Matrix.toLin' Q.transpose) h
  simpa only [← Matrix.toLin'_mul_apply, hQ, Matrix.toLin'_one, LinearMap.id_apply] using ht

theorem nystrom_orthonormal_range_basis {n l : ℕ} (A : RealMatrix n)
    (Ω Q : Matrix (Fin n) (Fin l) ℝ) (hΩ : FullColumns Ω)
    (hQ : Q.transpose * Q = 1) (hr : SameRange Ω Q) :
    nystrom A Q = nystrom A Ω :=
  nystrom_same_range A Ω Q hΩ (fullColumns_of_orthonormal Q hQ) hr

#print axioms same_range_change_of_basis
#print axioms nystrom_same_range
#print axioms fullColumns_of_orthonormal
#print axioms nystrom_orthonormal_range_basis
end NLA.RA08.Paper.RangeBasis
