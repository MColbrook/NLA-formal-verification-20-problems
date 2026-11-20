module

public import NLA.RA08.MatrixContour.Complexification
public import NLA.RA08.LiteralContour.ScalarCircle
public import NLA.RA08.LiteralContour.ContourRemainder

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical Matrix BigOperators Real Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem circleIntegral_clm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : ℂ → E) (c : ℂ) (r : ℝ) (hf : CircleIntegrable f c r) :
    L (∮ z in C(c,r), f z)=∮ z in C(c,r), L (f z) := by
  have h := L.intervalIntegral_comp_comm hf.out
  simpa only [circleIntegral,map_smul] using h.symm

def matrixEntryCLM (n : ℕ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  ({ toFun := fun A => A i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem circleIntegral_matrix_entry {n : ℕ} (f : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (r : ℝ) (hf : CircleIntegrable f c r) (i j : Fin n) :
    (∮ z in C(c,r), f z) i j=∮ z in C(c,r), f z i j :=
  circleIntegral_clm (matrixEntryCLM n i j) f c r hf

theorem circleIntegrable_matrix_entry {n : ℕ} (f : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (r : ℝ) (hf : CircleIntegrable f c r) (i j : Fin n) :
    CircleIntegrable (fun z => f z i j) c r := by
  exact ⟨(matrixEntryCLM n i j).integrable_comp hf.1,
    (matrixEntryCLM n i j).integrable_comp hf.2⟩

#print axioms circleIntegral_matrix_entry
end NLA.RA08.Paper.MatrixContour
