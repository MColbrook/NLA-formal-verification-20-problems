module

/- Endpoint recovery includes equality at the lower bracket; literal quarter-gap midpoint bound. -/
public import NLA.IV04.ExactOutputSupport.Recovery

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04ExactOutputSupport

 theorem near_optimum_candidate_exact_weak {q maximum L : ℚ} {Q : ℕ}
    (hQ : 0 < Q) (hq : q.den ≤ Q) (hmax : maximum.den ≤ Q)
    (hqmax : q ≤ maximum) (hLq : L ≤ q)
    (hgap : maximum-L < 1/(Q : ℚ)^2) : q=maximum := by
  exact unique_rational_in_narrow_bracket hQ hq hmax hLq hqmax
    (hLq.trans hqmax) le_rfl hgap

 theorem midpoint_quarter_gap {q : ℚ} {L U : ℝ} {Q : ℕ}
    (hLq : L ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ U)
    (hwidth : U-L < 1/(2*(Q : ℝ)^2)) :
    |(L+U)/2-(q : ℝ)| < 1/(4*(Q : ℝ)^2) := by
  calc
    |(L+U)/2-(q : ℝ)| ≤ (U-L)/2 := midpoint_error_bound hLq hqU
    _ < (1/(2*(Q : ℝ)^2))/2 := div_lt_div_of_pos_right hwidth (by norm_num)
    _ = 1/(4*(Q : ℝ)^2) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

#print axioms near_optimum_candidate_exact_weak
#print axioms midpoint_quarter_gap
end Reference.IV04ExactOutputSupport
