module

public import NLA.MD06.NonbacktrackingFoundation.Algebra
public import NLA.MD06.CubicConfiguration.CubicFrames
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_matching_rect_left_mul {n m : ℕ} (p : Pairing n)
    (B : Matrix (Dart n) (Fin m) ℝ) (a : Dart n) (b : Fin m) :
    (MatchingMatrix p * B) a b = B (p.val a) b := by
  simp [Matrix.mul_apply,MatchingMatrix]

theorem actual_adjacency_port_sum {n : ℕ} (p : Pairing n) (u v : Fin n) :
    AdjacencyMatrix p u v = ∑ a : Fin 3, if (p.val (u,a)).1=v then 1 else 0 := by
  rw [AdjacencyMatrix,Matrix.mul_assoc,Matrix.mul_apply]
  simp_rw [actual_matching_rect_left_mul]
  change (∑ a : Fin n × Fin 3, (if u=a.1 then (1 : ℝ) else 0) *
    (if v=(p.val a).1 then 1 else 0)) = _
  rw [Fintype.sum_prod_type]
  simp only [ite_mul,one_mul,zero_mul]
  simp [eq_comm]

theorem actual_configuration_adjacency_matrix {n : ℕ} (p : SimpleConfiguration n) :
    AdjacencyMatrix p.val = (configurationGraph p).adjMatrix ℝ := by
  ext u v
  rw [actual_adjacency_port_sum,SimpleGraph.adjMatrix_apply]
  change (∑ a : Fin 3, if (p.val.val (u,a)).1=v then (1 : ℝ) else 0) =
    @ite ℝ (∃ a : Fin 3, (p.val.val (u,a)).1=v) (Classical.propDecidable _) 1 0
  by_cases h : ∃ a : Fin 3, (p.val.val (u,a)).1=v
  · obtain ⟨a,ha⟩ := h
    rw [if_pos ⟨a,ha⟩]
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hba
      have hb : (p.val.val (u,b)).1 ≠ v := by
        intro hb
        exact hba (p.property.2 u (hb.trans ha.symm))
      simp [hb]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    have ha : (p.val.val (u,a)).1 ≠ v := by intro ha;exact h ⟨a,ha⟩
    simp [ha]

theorem actual_configuration_laplacian_matrix {n : ℕ} (p : SimpleConfiguration n) :
    (configurationGraph p).lapMatrix ℝ = (3 : ℝ) • 1 - AdjacencyMatrix p.val := by
  rw [SimpleGraph.lapMatrix,actual_configuration_adjacency_matrix]
  congr 1
  ext u v
  by_cases h : u=v <;>
    simp [SimpleGraph.degMatrix,(actual_configuration_graph_cubic p).degree_eq,
      h]

#print axioms actual_matching_rect_left_mul

#print axioms actual_adjacency_port_sum

#print axioms actual_configuration_adjacency_matrix

#print axioms actual_configuration_laplacian_matrix
end Reference.MD06Nonbacktracking
