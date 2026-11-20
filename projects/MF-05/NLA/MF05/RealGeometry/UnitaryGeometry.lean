module

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original comparison argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Matrix unitary conjugations are connected to Mathlib's genuine C*-norm.
The scoped matrix norm below is exactly the Euclidean operator norm wrapper.
-/
public import NLA.MF05.RealGeometry.Basics
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

set_option autoImplicit false
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace NLA.MF05.RealGeometry

lemma isUnitary_mem {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) :
    Q ∈ Matrix.unitaryGroup (Fin d) ℝ := by
  simpa only [IsUnitary, Unitary.mem_iff, Matrix.star_eq_conjTranspose] using hQ

lemma isUnitary_star {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) :
    IsUnitary Q.conjTranspose := by
  simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hQ.2 hQ.1

lemma spectralNorm_unitary_left {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) (A : Square d) :
    spectralNorm (Q * A) = spectralNorm A := by
  simpa only [spectralNorm, ← Matrix.cstar_norm_def] using
    CStarRing.norm_mem_unitary_mul A (isUnitary_mem hQ)

lemma spectralNorm_unitary_right {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) (A : Square d) :
    spectralNorm (A * Q) = spectralNorm A := by
  simpa only [spectralNorm, ← Matrix.cstar_norm_def] using
    CStarRing.norm_mul_mem_unitary A (isUnitary_mem hQ)

lemma spectralNorm_unitary_conj {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) (A : Square d) :
    spectralNorm (Q * A * Q.conjTranspose) = spectralNorm A := by
  rw [spectralNorm_unitary_right (isUnitary_star hQ), spectralNorm_unitary_left hQ]


end NLA.MF05.RealGeometry
