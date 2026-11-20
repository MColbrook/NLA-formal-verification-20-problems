module

public import NLA.PF02.GlobalOrientation.Reflection
public import NLA.PF02.GlobalOrientation.Coordinates

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper
open scoped BigOperators

theorem ordered_reflection_mask {n : ℕ} (p q : SymIndex n) (hp : p.1.1 ≠ p.1.2) :
    reflectionMask p.1.1 p.1.2 q.1.1 q.1.2 = if q = p then -1 else 1 := by
  have h : ((q.1.1 = p.1.1 ∧ q.1.2 = p.1.2) ∨ (q.1.1 = p.1.2 ∧ q.1.2 = p.1.1)) ↔ q = p := by
    constructor
    · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
      · exact Subtype.ext (Prod.ext ha hb)
      · have hrev : p.1.2 ≤ p.1.1 := by simpa only [ha,hb] using q.property
        exact (hp (le_antisymm p.property hrev)).elim
    · rintro rfl
      exact Or.inl ⟨rfl,rfl⟩
  simp only [reflectionMask, h]

theorem coordinate_reflection_det {n : ℕ}
    (C : SymIndex n → Matrix (Fin n) (Fin n) ℝ) (p : SymIndex n) (hp : p.1.1 ≠ p.1.2) :
    (coordinateRows (fun q => entryReflection p.1.1 p.1.2 (C q))).det = -(coordinateRows C).det := by
  classical
  have he : coordinateRows (fun q => entryReflection p.1.1 p.1.2 (C q)) =
      coordinateRows C * Matrix.diagonal (fun q : SymIndex n => if q = p then -1 else 1) := by
    ext a b
    simp only [coordinateRows, entryReflection, ordered_reflection_mask p b hp, Matrix.mul_diagonal]
    ring
  rw [he, Matrix.det_mul, Matrix.det_diagonal]
  simp

#print axioms ordered_reflection_mask
#print axioms coordinate_reflection_det
end Reference.PF02GlobalOrientation
