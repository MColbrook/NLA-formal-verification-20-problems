module

public import NLA.RA08.PaperNuclearNystromPositive
public import NLA.RA08.PaperNuclearTailDefinitions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearLiftVector_dot (m : ℕ) (η : ℝ) (x : Fin (m+m+1) → ℝ) :
    nuclearLiftVector m η ⬝ᵥ x =
      Real.sqrt η*(nuclearUnitVector m ⬝ᵥ (fun i => x i.castSucc))+
        Real.sqrt (1-η)*x (Fin.last (m+m)) := by
  simp only [dotProduct,Fin.sum_univ_castSucc,nuclearLiftVector,
    Fin.snoc_castSucc,Fin.snoc_last,mul_assoc,← Finset.mul_sum]

theorem nuclearLift_prefix_cauchy (m : ℕ) (hm : 1 ≤ m)
    (x : Fin (m+m+1) → ℝ) :
    (nuclearUnitVector m ⬝ᵥ (fun i => x i.castSucc))^2 ≤
      ∑ i : Fin (m+m), (x i.castSucc)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (nuclearUnitVector m) (fun i : Fin (m+m) => x i.castSucc)
  simpa [nuclearUnitVector_norm_sq m hm,dotProduct] using h

theorem nuclearLift_base_energy_lower (m : ℕ) (x : Fin (m+m+1) → ℝ) :
    (3/4 : ℝ)*(∑ i : Fin (m+m), (x i.castSucc)^2) ≤
      ∑ i : Fin (m+m), nuclearBaseEntries m i*(x i.castSucc)^2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (nuclearBaseEntries_lower m i) (sq_nonneg _)

/-- A sum-of-squares certificate for the actual lifted quadratic form. -/
theorem nuclearLift_energy_certificate (m : ℕ) (η t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x : Fin (m+m+1) → ℝ) :
    let S := ∑ i : Fin (m+m), nuclearBaseEntries m i*(x i.castSucc)^2
    let X := ∑ i : Fin (m+m), (x i.castSucc)^2
    let w := nuclearUnitVector m ⬝ᵥ (fun i => x i.castSucc)
    let z := x (Fin.last (m+m))
    let c := nuclearLiftTailLower η t
    x ⬝ᵥ (nuclearLiftA m η t *ᵥ x)-c*(X+z^2) =
      (S-(3/4)*X)+(1/4-c)*X+(1/2)*(X-w^2)+t*η*w^2+
        (1/2)*(w+2*t*Real.sqrt η*Real.sqrt (1-η)*z)^2 := by
  dsimp only
  rw [nuclearLiftA_energy,nuclearLiftVector_dot]
  have hsη := Real.sq_sqrt hη0
  have hsα := Real.sq_sqrt (show 0 ≤ 1-η by linarith)
  unfold nuclearLiftTailLower
  ring_nf
  simp only [hsη,hsα]
  ring

theorem nuclearLiftTailLower_le_time (η t : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (ht : 0 ≤ t) : nuclearLiftTailLower η t ≤ t := by
  have hα : (1-η)*t ≤ t := by nlinarith
  have hc : 0 ≤ 2*η*(1-η)*t^2 := by positivity
  unfold nuclearLiftTailLower
  linarith

theorem nuclearLift_energy_lower (m : ℕ) (hm : 1 ≤ m) (η t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/4)
    (x : Fin (m+m+1) → ℝ) :
    nuclearLiftTailLower η t*(∑ i : Fin (m+m+1), (x i)^2) ≤
      x ⬝ᵥ (nuclearLiftA m η t *ᵥ x) := by
  have hX : 0 ≤ ∑ i : Fin (m+m), (x i.castSucc)^2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hbase := nuclearLift_base_energy_lower m x
  have hca := nuclearLift_prefix_cauchy m hm x
  have hc : nuclearLiftTailLower η t ≤ 1/4 :=
    (nuclearLiftTailLower_le_time η t hη0 hη1 ht0).trans ht1
  have h1 : 0 ≤ (1/4-nuclearLiftTailLower η t)*
      (∑ i : Fin (m+m), (x i.castSucc)^2) := mul_nonneg (by linarith) hX
  have h2 : 0 ≤ t*η*(nuclearUnitVector m ⬝ᵥ (fun i => x i.castSucc))^2 := by positivity
  have h3 := sq_nonneg ((nuclearUnitVector m ⬝ᵥ (fun i => x i.castSucc))+
    2*t*Real.sqrt η*Real.sqrt (1-η)*x (Fin.last (m+m)))
  have he := nuclearLift_energy_certificate m η t hη0 hη1 x
  dsimp only at he
  rw [Fin.sum_univ_castSucc]
  linarith

#print axioms nuclearLift_energy_lower
end NLA.RA08.Paper
