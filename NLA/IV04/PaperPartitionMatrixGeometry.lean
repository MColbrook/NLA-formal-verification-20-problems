module

public import NLA.IV04.PaperPartitionMatrixOutputSemantics
public import NLA.IV04.PaperSATWeightTableLayout
public import NLA.IV04.PaperConstructedBox
public import NLA.IV04.PaperRealIntervalVertex
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational

theorem partition_endpoint_pairs_ofFn (P : IV04.Paper.IntegerPartition) :
    partitionMatrixEndpointPairs P = List.ofFn (fun k : Fin (P.layerCount*P.layerCount) =>
      (P.rationalLower (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2,
       P.rationalUpper (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) := by
  have h := sat_table_ofFn_prod (fun ij : Fin P.layerCount × Fin P.layerCount =>
    (P.rationalLower ij.1 ij.2,P.rationalUpper ij.1 ij.2))
  unfold partitionMatrixEndpointPairs partitionMatrixIndexPairs
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  simpa only [List.ofFn_eq_map,List.flatMap_def,Function.comp_def] using h.symm

theorem partition_endpoint_pairs_length (P : IV04.Paper.IntegerPartition) :
    (partitionMatrixEndpointPairs P).length = P.layerCount*P.layerCount := by
  rw [partition_endpoint_pairs_ofFn]
  simp

theorem partition_endpoint_pairs_getD (P : IV04.Paper.IntegerPartition)
    (i j : Fin P.layerCount) :
    (partitionMatrixEndpointPairs P).getD (i.val*P.layerCount+j.val) (0,0) =
      (P.rationalLower i j,P.rationalUpper i j) := by
  have hk : i.val*P.layerCount+j.val < P.layerCount*P.layerCount := by
    nlinarith [i.isLt,j.isLt]
  have he : finProdFinEquiv.symm (⟨i.val*P.layerCount+j.val,hk⟩ :
      Fin (P.layerCount*P.layerCount)) = (i,j) := by
    apply (finProdFinEquiv : Fin P.layerCount × Fin P.layerCount ≃
      Fin (P.layerCount*P.layerCount)).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change i.val*P.layerCount+j.val=j.val+P.layerCount*i.val
    ac_rfl
  rw [partition_endpoint_pairs_ofFn]
  simp only [List.getD, List.getElem?_ofFn, dif_pos hk, Option.getD_some, he]

theorem partition_endpoint_pairs_ordered (P : IV04.Paper.IntegerPartition) :
    ∀ row ∈ partitionMatrixEndpointPairs P, row.1  ≤  row.2 := by
  intro row hrow
  obtain ⟨ij,_,rfl⟩ := List.mem_map.mp hrow
  exact P.intervalBox.ordered ij.1 ij.2

theorem partition_endpoints_offband_zero (P : IV04.Paper.IntegerPartition)
    (i j : Fin P.layerCount) (hoff : i.val+1 < j.val ∨ j.val+1 < i.val) :
    P.rationalLower i j=0 ∧ P.rationalUpper i j=0 := by
  have he : i≠j := by intro h; subst j; omega
  have hu : j.val≠i.val+1 := by omega
  have hl : i.val≠j.val+1 := by omega
  simp [IV04.Paper.IntegerPartition.rationalLower,
    IV04.Paper.IntegerPartition.rationalUpper,he,hu,hl]

theorem rational_dense_all_of_address (n i j : ℕ) (pairs : List (ℚ × ℚ))
    (hj : j < n)
    (h : ∀ k a b : ℕ, k < pairs.length → b < n → i*n+j+k=a*n+b →
      (a ≤ b+1 ∧ b ≤ a+1) ∨ ((pairs.getD k (0,0)).1=0 ∧ (pairs.getD k (0,0)).2=0)) :
    rationalDenseEndpointAll n i j pairs := by
  induction pairs generalizing i j with
  | nil => trivial
  | cons row rows ih =>
    change ((i ≤ j+1 ∧ j ≤ i+1) ∨ (row.1=0 ∧ row.2=0)) ∧ _
    constructor
    · simpa using h 0 i j (by simp) hj (by omega)
    · have hs := dense_row_cursor_successor n i j hj
      apply ih (if n ≤ j+1 then i+1 else i) (if n ≤ j+1 then 0 else j+1) hs.2
      intro k a b hk hb ha
      have ha' : i*n+j+(k+1)=a*n+b := by rw [hs.1] at ha; omega
      simpa using h (k+1) a b (by simpa using Nat.succ_lt_succ hk) hb ha'

theorem partition_endpoint_pairs_support (P : IV04.Paper.IntegerPartition) :
    rationalDenseEndpointAll P.layerCount 0 0 (partitionMatrixEndpointPairs P) := by
  have hn : 0 < P.layerCount := by
    have hp := P.nonempty
    dsimp [IV04.Paper.IntegerPartition.layerCount]
    omega
  apply rational_dense_all_of_address P.layerCount 0 0 (partitionMatrixEndpointPairs P) hn
  intro k a b hk hb ha
  have hk' : k < P.layerCount*P.layerCount := by rwa [partition_endpoint_pairs_length] at hk
  have he : k=a*P.layerCount+b := by simpa using ha
  have ha' : a < P.layerCount := by nlinarith
  by_cases hband : a ≤ b+1 ∧ b ≤ a+1
  · exact Or.inl hband
  · right
    have hz := partition_endpoints_offband_zero P ⟨a,ha'⟩ ⟨b,hb⟩ (by dsimp;omega)
    rw [he,partition_endpoint_pairs_getD P ⟨a,ha'⟩ ⟨b,hb⟩]
    exact hz

theorem partition_real_dense_box_exact (P : IV04.Paper.IntegerPartition) :
    realDenseIntervalBox P.layerCount (partitionMatrixEndpointPairs P) =
      P.intervalBox.realizations := by
  ext A
  change (∀ i j, _ ∧ _) ↔ (∀ i j, _ ∧ _)
  simp only [boxLowerReal,boxUpperReal,partition_endpoint_pairs_getD]
  rfl

#print axioms partition_endpoint_pairs_ofFn
#print axioms partition_endpoint_pairs_length
#print axioms partition_endpoint_pairs_getD
#print axioms partition_endpoint_pairs_ordered
#print axioms partition_endpoints_offband_zero
#print axioms rational_dense_all_of_address
#print axioms partition_endpoint_pairs_support
#print axioms partition_real_dense_box_exact
end IV04.Paper.Computational
