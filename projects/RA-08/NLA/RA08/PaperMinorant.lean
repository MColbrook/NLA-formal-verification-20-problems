module

public import NLA.RA08.Polynomial

@[expose] public section

/- Draft scalar strengthening; requires actual Lean compilation before packaging. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.RA08.Paper

def correction (x : ℝ) : ℝ := minorantCoefficient +
  (-20401094656 / 32234193 : ℝ) * (x-witnessA) + 10000*(x-witnessA)^2
def paperMinorant (x : ℝ) : ℝ := x - (cubicFunction x)^2 * correction x

theorem correction_nonneg (x : ℝ) : 0 ≤ correction x := by
  have hid : correction x = 10000 * (x-witnessA + (-637534208 / 20146370625 : ℝ))^2 +
      (16480802926311243776 / 649401998975780625 : ℝ) := by
    unfold correction minorantCoefficient
    ring
  rw [hid]
  positivity

theorem paperMinorant_le (x : ℝ) (hgap : x ≤ 1 ∨ witnessA ≤ x) :
    paperMinorant x ≤ witnessFunction x := by
  rcases hgap with hx | hx
  · rw [witnessFunction, min_eq_left hx]
    exact sub_le_self _ (mul_nonneg (sq_nonneg _) (correction_nonneg x))
  · have h1 : 1 ≤ x := by unfold witnessA at hx; linarith
    have hy : 0 ≤ x-witnessA := sub_nonneg.mpr hx
    have hid : (cubicFunction x)^2 * correction x - (x-1) =
        (x-witnessA)^2 * ((4353307940257 / 1570951397376 : ℝ) +
          (1420779232985 / 5151653888 : ℝ) * (x-witnessA)^1 +
          (21396454633338331 / 4225000144896 : ℝ) * (x-witnessA)^2 +
          (2954679181440181 / 132031254528 : ℝ) * (x-witnessA)^3 +
          (1348982610759505 / 33007813632 : ℝ) * (x-witnessA)^4 +
          (4290158047001 / 128936772 : ℝ) * (x-witnessA)^5 +
          (10000 / 1 : ℝ) * (x-witnessA)^6) := by
      unfold cubicFunction correction minorantCoefficient witnessA witnessB
      ring
    have hnonneg : 0 ≤ (cubicFunction x)^2 * correction x - (x-1) := by
      rw [hid]
      positivity
    rw [witnessFunction, min_eq_right h1]
    unfold paperMinorant
    linarith

#print axioms paperMinorant_le
end NLA.RA08.Paper
