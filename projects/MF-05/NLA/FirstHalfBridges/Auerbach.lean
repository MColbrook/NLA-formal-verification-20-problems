module

public import NLA.FirstHalfBridges.Definitions
public import NLA.MF07.Auerbach
public import NLA.MF05.RealGeometry.Auerbach

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace RootFirstHalfBridges

section
open NLA.MF07
theorem actual_complex_maximal_columns {d : ℕ} {v : EuclideanVector d → ℝ}
    (hv : IsComplexNorm v) (T : Square d) (hT : T.det ≠ 0)
    (hcol : ∀ j, v (WithLp.toLp 2 (fun i => T i j)) ≤ 1)
    (hmax : ∀ S : Square d, (∀ j, v (WithLp.toLp 2 (fun i => S i j)) ≤ 1) → ‖S.det‖ ≤ ‖T.det‖) :
    ∀ j, v (WithLp.toLp 2 (fun i => T i j)) = 1 := by
  intro j
  have he : applyMatrix T (coordinateUnit j) = matrixColumn T j := by
    ext i
    simp [applyMatrix_coordinate,matrixColumn_apply]
  have hce (S : Square d) (k : Fin d) : matrixColumn S k = WithLp.toLp 2 (fun i => S i k) := by
    ext i
    simp [matrixColumn_apply]
  have hl := maximal_basis_coordinate_bound hv T hT
    (fun k => by rw [hce]; exact hcol k)
    (fun S hs => hmax S (fun k => by rw [← hce]; exact hs k)) (coordinateUnit j) j
  rw [he] at hl
  apply le_antisymm (hcol j)
  simpa [coordinateUnit_apply,hce] using hl
end
section
open NLA.MF05.RealGeometry
theorem actual_real_maximal_columns {d : ℕ} {v : EuclideanVector d → ℝ}
    (hv : IsNorm v) (T : Square d) (hT : T.det ≠ 0)
    (hcol : ∀ j, v (WithLp.toLp 2 (fun i => T i j)) ≤ 1)
    (hmax : ∀ S : Square d, (∀ j, v (WithLp.toLp 2 (fun i => S i j)) ≤ 1) → ‖S.det‖ ≤ ‖T.det‖) :
    ∀ j, v (WithLp.toLp 2 (fun i => T i j)) = 1 := by
  intro j
  have he : applyMatrix T (coordinateUnit j) = matrixColumn T j := by
    ext i
    simp [applyMatrix_coordinate,matrixColumn_apply]
  have hce (S : Square d) (k : Fin d) : matrixColumn S k = WithLp.toLp 2 (fun i => S i k) := by
    ext i
    simp [matrixColumn_apply]
  have hl := maximal_basis_coordinate_bound hv T hT
    (fun k => by rw [hce]; exact hcol k)
    (fun S hs => hmax S (fun k => by rw [← hce]; exact hs k)) (coordinateUnit j) j
  rw [he] at hl
  apply le_antisymm (hcol j)
  simpa [coordinateUnit_apply,hce] using hl
end

#print axioms actual_complex_maximal_columns
#print axioms actual_real_maximal_columns
end RootFirstHalfBridges
