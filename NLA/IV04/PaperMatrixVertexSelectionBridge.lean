module

public import NLA.IV04.PaperMatrixVertexSelectionSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem endpoint_word_pairs_code_flatten (rows : List (List Bool × List Bool)) (rest : List (List Bool)) :
    endpointWordPairsCode rows (payloadListCode rest)=
      payloadListCode (rows.flatMap (fun row => [row.1,row.2])++rest) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => obtain ⟨lower,upper⟩ := row; simp [endpointWordPairsCode,payloadListCode,ih]

theorem scaled_endpoint_words_split (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (denominator : ℕ) (coefficients : List (List Bool))
    (h : coefficients.map (fun word => (signedWordValue word : ℚ))=
      (pairs.flatMap (fun row => [row.1,row.2])++[threshold]).map
        (fun q => q*(denominator : ℚ))) :
    ∃ rows : List (List Bool × List Bool), ∃ thresholdWord : List Bool,
      coefficients=rows.flatMap (fun row => [row.1,row.2])++[thresholdWord] ∧
      rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
        pairs.map (fun row => (row.1*(denominator : ℚ),row.2*(denominator : ℚ))) ∧
      (signedWordValue thresholdWord : ℚ)=threshold*(denominator : ℚ) := by
  induction pairs generalizing coefficients with
  | nil =>
    have hl : coefficients.length=1 := by
      have hlen := congrArg List.length h
      simpa using hlen
    cases coefficients with
    | nil => simp at hl
    | cons word words =>
      have he : words=[] := by cases words <;> simp_all
      subst words
      refine ⟨[],word,rfl,rfl,?_⟩
      simpa using h
  | cons row pairs ih =>
    obtain ⟨lower,upper⟩ := row
    cases coefficients with
    | nil => simp at h
    | cons left coefficients =>
      cases coefficients with
      | nil => simp at h
      | cons right coefficients =>
        simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.map_cons,List.map_append,
          List.map_nil,List.cons.injEq] at h
        obtain ⟨hl,hr,ht⟩ := h
        have ht' : coefficients.map (fun word => (signedWordValue word : ℚ))=
            (pairs.flatMap (fun row => [row.1,row.2])++[threshold]).map
              (fun q => q*(denominator : ℚ)) := by
          simpa only [List.map_append,List.map_cons,List.map_nil] using ht
        obtain ⟨rows,tword,he,hrows,hthreshold⟩ := ih coefficients ht'
        refine ⟨(left,right)::rows,tword,?_,?_,hthreshold⟩
        · simp [he]
        · simp [hl,hr,hrows]

theorem scaled_endpoint_words_ordered (pairs : List (ℚ × ℚ)) (rows : List (List Bool × List Bool))
    (denominator : ℕ) (hD : 0 < denominator)
    (hmap : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(denominator : ℚ),row.2*(denominator : ℚ))))
    (ho : ∀ row ∈ pairs, row.1 ≤ row.2) : endpointWordsOrdered rows := by
  intro row hr
  have hm : ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)) ∈
      pairs.map (fun row => (row.1*(denominator : ℚ),row.2*(denominator : ℚ))) := by
    rw [←hmap]
    exact List.mem_map.mpr ⟨row,hr,rfl⟩
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hm
  have hl : (signedWordValue row.1 : ℚ)=p.1*(denominator : ℚ) := (congrArg Prod.fst he).symm
  have hu : (signedWordValue row.2 : ℚ)=p.2*(denominator : ℚ) := (congrArg Prod.snd he).symm
  have hd : (0 : ℚ) ≤ denominator := le_of_lt (by exact_mod_cast hD)
  have hle : (signedWordValue row.1 : ℚ) ≤ (signedWordValue row.2 : ℚ) := by
    rw [hl,hu]
    exact mul_le_mul_of_nonneg_right (ho p hp) hd
  exact_mod_cast hle

#print axioms scaled_endpoint_words_split
end IV04.Paper.Computational
