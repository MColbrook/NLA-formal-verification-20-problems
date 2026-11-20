module

public import NLA.RA08.RangeBasis.Range
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix Module
namespace NLA.RA08.Paper.RangeBasis

theorem exists_orthonormal_range_basis {n l : ℕ}
    (Ω : Matrix (Fin n) (Fin l) ℝ) (hΩ : FullColumns Ω) :
    ∃ Q : Matrix (Fin n) (Fin l) ℝ, Q.transpose * Q = 1 ∧ SameRange Ω Q := by
  let en := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let f := en.symm.toLinearMap.comp (Matrix.toLin' Ω)
  have hf : Function.Injective f := en.symm.injective.comp hΩ
  let S := LinearMap.range f
  have hd : finrank ℝ S = l := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one]
      using LinearMap.finrank_range_of_inj hf
  let b : OrthonormalBasis (Fin l) ℝ S :=
    (stdOrthonormalBasis ℝ S).reindex (finCongr hd)
  let e := b.toBasis.equivFun.symm
  let g := en.toLinearMap.comp (S.subtype.comp e.toLinearMap)
  let Q := LinearMap.toMatrix' g
  have hcol (i : Fin n) (j : Fin l) : Q i j = (b j).val i := by
    simp only [Q, LinearMap.toMatrix'_apply, g, LinearMap.comp_apply,
      Submodule.subtype_apply, e]
    simp
    rfl
  refine ⟨Q, ?_, ?_⟩
  · ext i j
    have hb := b.inner_eq_ite i j
    change (∑ k, (b j).val k * (b i).val k) = if i = j then 1 else 0 at hb
    change (∑ k, Q k i * Q k j) = if i = j then 1 else 0
    calc
      (∑ k, Q k i * Q k j) = ∑ k, (b j).val k * (b i).val k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hcol, hcol, mul_comm]
      _ = if i = j then 1 else 0 := hb
  · change LinearMap.range (Matrix.toLin' Ω) = LinearMap.range (Matrix.toLin' Q)
    rw [Matrix.toLin'_toMatrix']
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      let z : S := ⟨f x, LinearMap.mem_range_self f x⟩
      refine ⟨e.symm z, ?_⟩
      change en (e (e.symm z)).val = (Matrix.toLin' Ω) x
      rw [e.apply_symm_apply]
      exact en.apply_symm_apply _
    · rintro ⟨x, rfl⟩
      obtain ⟨z, hz⟩ := (e x).property
      refine ⟨z, ?_⟩
      change (Matrix.toLin' Ω) z = en (e x).val
      calc
        (Matrix.toLin' Ω) z = en (f z) := (en.apply_symm_apply _).symm
        _ = en (e x).val := congrArg en hz

theorem nystrom_has_orthonormal_sketch {n l : ℕ} (A : RealMatrix n)
    (Ω : Matrix (Fin n) (Fin l) ℝ) (hΩ : FullColumns Ω) :
    ∃ Q : Matrix (Fin n) (Fin l) ℝ,
      Q.transpose * Q = 1 ∧ SameRange Ω Q ∧ nystrom A Q = nystrom A Ω := by
  obtain ⟨Q, hQ, hr⟩ := exists_orthonormal_range_basis Ω hΩ
  exact ⟨Q, hQ, hr, nystrom_orthonormal_range_basis A Ω Q hΩ hQ hr⟩

#print axioms exists_orthonormal_range_basis
#print axioms nystrom_has_orthonormal_sketch
end NLA.RA08.Paper.RangeBasis
