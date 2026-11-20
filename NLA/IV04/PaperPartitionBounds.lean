module

public import NLA.IV04.PaperPartitionRotations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace IV04.Paper

theorem arctan_cubic_error (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ 2*t-2*Real.arctan t ∧ 2*t-2*Real.arctan t ≤ (2/3)*t^3 := by
  have hf : ∀ x : ℝ, HasDerivAt (fun y => y-Real.arctan y) (1-1/(1+x^2)) x :=
    fun x => (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
  have hm := monotone_of_hasDerivAt_nonneg hf (by
    intro x
    change 0 ≤ 1-1/(1+x^2)
    have hd : 0 < 1+x^2 := by positivity
    have he : 1-1/(1+x^2)=x^2/(1+x^2) := by field_simp; ring
    rw [he]
    positivity)
  have hg : ∀ x : ℝ, HasDerivAt (fun y => Real.arctan y-y+y^3/3)
      (1/(1+x^2)-1+(3*x^2)/3) x := by
    intro x
    have hsub : HasDerivAt (fun y : ℝ => Real.arctan y-y) (1/(1+x^2)-1) x :=
      (Real.hasDerivAt_arctan x).sub (hasDerivAt_id x)
    have hpow : HasDerivAt (fun y : ℝ => y^3/3) (3*x^2/3) x := by
      simpa using (HasDerivAt.div_const (hasDerivAt_pow 3 x) 3)
    exact hsub.add hpow
  have hn := monotone_of_hasDerivAt_nonneg hg (by
    intro x
    change 0 ≤ 1/(1+x^2)-1+(3*x^2)/3
    have hd : 0 < 1+x^2 := by positivity
    have he : 1/(1+x^2)-1+(3*x^2)/3=x^4/(1+x^2) := by field_simp; ring
    rw [he]
    positivity)
  have h1 := hm ht
  have h2 := hn ht
  simp only [Real.arctan_zero,zero_pow,zero_div,sub_zero,zero_add] at h1 h2
  constructor <;> linarith

theorem cosine_quadratic_upper (x : ℝ) (hx : |x| ≤ 1) :
    Real.cos x ≤ 1-x^2/3 := by
  have hb := (abs_le.mp (Real.cos_bound hx)).2
  have hsq : |x|^2=x^2 := sq_abs x
  have hsmall : |x|^2 ≤ 1 := by nlinarith [abs_nonneg x]
  have hfour : |x|^4 ≤ x^2 := by
    nlinarith [mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hsmall)]
  nlinarith

theorem sum_cubes_le_cube_sum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∑ i ∈ S, f i^3) ≤ (∑ i ∈ S, f i)^3 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have h0 : 0 ≤ f a := hf a (Finset.mem_insert_self a S)
    have hS : ∀ i ∈ S, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum := Finset.sum_nonneg hS
    have hb := ih hS
    nlinarith [mul_nonneg h0 (sq_nonneg (∑ i ∈ S, f i)),
      mul_nonneg (sq_nonneg (f a)) hsum]

namespace IntegerPartition

theorem sum_t (P : IntegerPartition) :
    (∑ i, (P.t i : ℝ)) = (P.delta : ℝ)*P.total := by
  simp only [t,Rat.cast_mul,Rat.cast_natCast,← Finset.mul_sum]
  norm_cast

theorem theta_nonneg (P : IntegerPartition) (i : Fin P.m) : 0 ≤ P.theta i := by
  have ht : (0 : ℝ) ≤ P.t i := by exact_mod_cast (t_pos P i).le
  exact mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr ht)

theorem theta_le_scaled_weight (P : IntegerPartition) (i : Fin P.m) :
    P.theta i ≤ 2*(P.delta : ℝ)*P.weight i := by
  have ht : (0 : ℝ) ≤ P.t i := by exact_mod_cast (t_pos P i).le
  have hb := (arctan_cubic_error (P.t i) ht).1
  simpa [theta,t,mul_assoc] using (show 2*Real.arctan (P.t i : ℝ) ≤ 2*(P.t i : ℝ) by linarith)

theorem total_angle_le (P : IntegerPartition) : (∑ i, P.theta i) ≤ 1/5 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => theta_le_scaled_weight P i)
  have hW : (1 : ℝ) ≤ P.total := by exact_mod_cast total_pos P
  have hd : 0 < 10*(P.total : ℝ)^2 := by positivity
  have hb : 2*(P.delta : ℝ)*P.total ≤ 1/5 := by
    push_cast [delta]
    have he : 2*(1/(10*(P.total : ℝ)^2))*(P.total : ℝ)=
        (2*(P.total : ℝ))/(10*(P.total : ℝ)^2) := by ring
    rw [he,div_le_iff₀ hd]
    nlinarith [sq_nonneg ((P.total : ℝ)-1)]
  calc
    (∑ i, P.theta i) ≤ ∑ i, 2*(P.delta : ℝ)*P.weight i := hs
    _ = 2*(P.delta : ℝ)*P.total := by simp [← Finset.mul_sum,total]
    _ ≤ 1/5 := hb

theorem error_le_cubic (P : IntegerPartition) :
    P.error ≤ (2/3)*((P.delta : ℝ)*P.total)^3 := by
  have hbound : ∀ i : Fin P.m,
      |P.theta i-2*(P.delta : ℝ)*P.weight i| ≤ (2/3)*(P.t i : ℝ)^3 := by
    intro i
    have ht : (0 : ℝ) ≤ P.t i := by exact_mod_cast (t_pos P i).le
    have hb := arctan_cubic_error (P.t i) ht
    have he : 2*(P.delta : ℝ)*(P.weight i : ℝ)=2*(P.t i : ℝ) := by simp [t,mul_assoc]
    rw [he,theta,abs_of_nonpos (by linarith)]
    linarith [hb.2]
  have hsum := sum_cubes_le_cube_sum Finset.univ (fun i : Fin P.m => (P.t i : ℝ))
    (fun i _ => by exact_mod_cast (t_pos P i).le)
  calc
    P.error ≤ ∑ i, (2/3)*(P.t i : ℝ)^3 := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (2/3)*∑ i, (P.t i : ℝ)^3 := by rw [Finset.mul_sum]
    _ ≤ (2/3)*(∑ i, (P.t i : ℝ))^3 := by gcongr
    _ = (2/3)*((P.delta : ℝ)*P.total)^3 := by rw [sum_t]

theorem cubic_error_identity (P : IntegerPartition) :
    (2/3)*((P.delta : ℝ)*P.total)^3 = (P.delta : ℝ)/(150*P.total) := by
  have hW : (P.total : ℝ) ≠ 0 := by exact_mod_cast (total_pos P).ne'
  push_cast [delta]
  field_simp [hW]
  <;> ring

theorem error_le_delta_tenth (P : IntegerPartition) : P.error ≤ (P.delta : ℝ)/10 := by
  have hW : (1 : ℝ) ≤ P.total := by exact_mod_cast total_pos P
  have hdelta : (0 : ℝ) < P.delta := by exact_mod_cast delta_pos P
  have hden : (0 : ℝ) < 150*P.total := by positivity
  have hb : (P.delta : ℝ)/(150*P.total) ≤ (P.delta : ℝ)/10 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have he : P.error ≤ (P.delta : ℝ)/(150*P.total) := by
    simpa [cubic_error_identity] using error_le_cubic P
  exact he.trans hb

end IntegerPartition
end IV04.Paper
