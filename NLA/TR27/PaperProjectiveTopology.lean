module

public import NLA.TR27.PaperProjectiveTopologyDefinitions
public import NLA.TR27.Semantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

theorem coordinateNormSq_ne_zero {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) :
    coordinateNormSq v ≠ 0 := by
  intro h
  apply hv
  ext i
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (v j))).mp h i
      (Finset.mem_univ _))

theorem coordinateNormSq_smul {n : ℕ} (c : ℂ) (v : Fin n → ℂ) :
    coordinateNormSq (c • v) = Complex.normSq c * coordinateNormSq v := by
  simp [coordinateNormSq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem coordinateProjector_smul {n : ℕ} (c : ℂ) (hc : c ≠ 0) (v : Fin n → ℂ) :
    coordinateProjector (c • v) = coordinateProjector v := by
  have hn : (Complex.normSq c : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_eq_zero.not.mpr hc)
  ext i j
  simp only [coordinateProjector, coordinateNormSq_smul, Pi.smul_apply, smul_eq_mul,
    star_mul', Complex.ofReal_mul]
  rw [show c * v i * (star c * star (v j)) =
    (Complex.normSq c : ℂ) * (v i * star (v j)) by
      rw [← Complex.mul_conj]; change c*v i*(star c*star (v j)) = c*star c*(v i*star (v j)); ring]
  exact mul_div_mul_left _ _ hn

theorem projectiveProjector_mk {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) :
    projectiveProjector (Projectivization.mk ℂ v hv) = coordinateProjector v := by
  obtain ⟨c,hc,heq⟩ := represents_mk v hv
  rw [projectiveProjector, heq, coordinateProjector_smul c hc]

theorem coordinateProjector_ratio {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0)
    (i j : Fin n) (hj : v j ≠ 0) :
    coordinateProjector v i j / coordinateProjector v j j = v i / v j := by
  have hn : (coordinateNormSq v : ℂ) ≠ 0 := by exact_mod_cast coordinateNormSq_ne_zero v hv
  have hj' : star (v j) ≠ 0 := star_ne_zero.mpr hj
  simp only [coordinateProjector]
  field_simp

theorem projectiveProjector_injective (n : ℕ) :
    Function.Injective (@projectiveProjector n) := by
  intro p q he
  obtain ⟨j,hj⟩ : ∃ j, p.rep j ≠ 0 := by
    by_contra h
    push Not at h
    exact p.rep_nonzero (funext h)
  have hp : (coordinateNormSq p.rep : ℂ) ≠ 0 := by
    exact_mod_cast coordinateNormSq_ne_zero p.rep p.rep_nonzero
  have hd : coordinateProjector p.rep j j ≠ 0 :=
    div_ne_zero (mul_ne_zero hj (star_ne_zero.mpr hj)) hp
  have hqj : q.rep j ≠ 0 := by
    intro hz
    apply hd
    change projectiveProjector p j j = 0
    rw [he]
    simp [projectiveProjector, coordinateProjector, hz]
  have hratio (i : Fin n) : p.rep i / p.rep j = q.rep i / q.rep j := by
    rw [← coordinateProjector_ratio p.rep p.rep_nonzero i j hj,
      ← coordinateProjector_ratio q.rep q.rep_nonzero i j hqj]
    change projectiveProjector p i j / projectiveProjector p j j = _
    rw [he]
    rfl
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q, Projectivization.mk_eq_mk_iff']
  refine ⟨p.rep j / q.rep j, ?_⟩
  ext i
  change (p.rep j / q.rep j)*q.rep i = p.rep i
  have hi := hratio i
  field_simp at hi ⊢
  exact hi.symm

theorem continuous_coordinateNormSq (n : ℕ) : Continuous (@coordinateNormSq n) := by
  unfold coordinateNormSq
  exact continuous_finsetSum _ (fun i _ => Complex.continuous_normSq.comp (continuous_apply i))

theorem continuous_coordinateProjector_nonzero (n : ℕ) :
    Continuous (fun v : {v : Fin n → ℂ // v ≠ 0} => coordinateProjector v.val) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply Continuous.div
  · exact ((continuous_apply i).comp continuous_subtype_val).mul
      (((continuous_apply j).comp continuous_subtype_val).star)
  · exact Complex.continuous_ofReal.comp ((continuous_coordinateNormSq n).comp continuous_subtype_val)
  · intro v
    exact_mod_cast coordinateNormSq_ne_zero v.val v.property

theorem continuous_projectiveProjector (n : ℕ) : Continuous (@projectiveProjector n) := by
  apply continuous_coinduced_dom.mpr
  have he : projectiveProjector ∘ Projectivization.mk' ℂ =
      fun v : {v : Fin n → ℂ // v ≠ 0} => coordinateProjector v.val := by
    funext v
    exact projectiveProjector_mk v.val v.property
  rw [he]
  exact continuous_coordinateProjector_nonzero n

theorem coordinateProjective_t2 (n : ℕ) : T2Space (ℙ ℂ (Fin n → ℂ)) :=
  T2Space.of_injective_continuous (projectiveProjector_injective n) (continuous_projectiveProjector n)

#print axioms coordinateProjective_t2
end NLA.TR27.Paper
