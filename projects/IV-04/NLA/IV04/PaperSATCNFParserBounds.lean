module

public import NLA.IV04.PaperSATCNFParserDefinitions
public import NLA.IV04.PaperSATRawLiteral
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

private theorem sat_parse_and_length (a b : List Bool) : (andBit a b).length=1 := by
  cases a with
  | nil => simp [andBit,caseBit₀]
  | cons x xs => cases x <;> cases b with
    | nil => simp [andBit,caseBit₀]
    | cons y ys => cases y <;> simp [andBit,caseBit₀]

private theorem sat_parse_head_length (a : List Bool) : (bitAt [] a).length=1 := by
  cases a with
  | nil => rfl
  | cons x xs => cases x <;> rfl

private theorem sat_parse_literal_payload_length (raw : List Bool) :
    (pairSnd (polynomialSATRawLiteral raw)).length ≤ 4*raw.length+3 := by
  have hn := (canonical_word_length (rawLengthWord raw.tail)).trans (raw_length_word_length raw.tail)
  have hh := sat_parse_head_length raw
  simp only [polynomialSATRawLiteral,pairSnd_pair,pair_length]
  simp only [inputLengthWord]
  have ht : raw.tail.length ≤ raw.length := by cases raw <;> simp
  omega

 theorem sat_cnf_pack_length (rest raw clause formula valid : List Bool) :
    (satCNFPack rest raw clause formula valid).length=
      2*rest.length+2*raw.length+2*clause.length+2*formula.length+valid.length+8 := by
  simp [satCNFPack,pair_length]
  omega

 theorem sat_cnf_step_nil (raw clause formula valid : List Bool) :
    satCNFParseStep (satCNFPack [] raw clause formula valid)=satCNFPack [] raw clause formula valid := by
  simp [satCNFParseStep,satCNFPack,satCNFRest,nonemptyFlag,caseBit₀,caseBit]

 theorem sat_cnf_step_single (b : Bool) (raw clause formula valid : List Bool) :
    satCNFParseStep (satCNFPack [b] raw clause formula valid)=satCNFPack [] raw clause formula [false] := by
  cases b <;> simp [satCNFParseStep,satCNFPack,satCNFRest,satCNFRaw,satCNFClause,satCNFFormula,
    nonemptyFlag,caseBit₀,caseBit]

 theorem sat_cnf_step_pair (a b : Bool) (rest raw clause formula valid : List Bool) :
    satCNFParseStep (satCNFPack (a::b::rest) raw clause formula valid)=
      if a=b then satCNFPack rest (raw++[a]) clause formula valid else
      if a then satCNFPack rest [] [] (pair clause formula) (andBit valid (notBit (nonemptyFlag raw))) else
        satCNFPack rest [] (pair (pairSnd (polynomialSATRawLiteral raw)) clause) formula
          (andBit valid (pairFst (polynomialSATRawLiteral raw))) := by
  cases a <;> cases b <;>
    simp [satCNFParseStep,satCNFPack,satCNFRest,satCNFRaw,satCNFClause,satCNFFormula,satCNFValid,
      nonemptyFlag,bitAt,caseBit₀,caseBit]

 theorem sat_cnf_step_shape (rest raw clause formula valid : List Bool) :
    ∃ r u c f v : List Bool,
      satCNFParseStep (satCNFPack rest raw clause formula valid)=satCNFPack r u c f v ∧
      2*r.length+32*u.length+4*c.length+2*f.length+v.length+8 ≤
        2*rest.length+32*raw.length+4*clause.length+2*formula.length+valid.length+8+40 := by
  cases rest with
  | nil =>
    refine ⟨[],raw,clause,formula,valid,sat_cnf_step_nil _ _ _ _,?_⟩
    omega
  | cons a tail =>
    cases tail with
    | nil =>
      refine ⟨[],raw,clause,formula,[false],sat_cnf_step_single _ _ _ _ _,?_⟩
      simp only [List.length_nil,List.length_cons]
      omega
    | cons b rest =>
      rw [sat_cnf_step_pair]
      have hl := sat_parse_literal_payload_length raw
      have hv := sat_parse_and_length valid (pairFst (polynomialSATRawLiteral raw))
      have hz := sat_parse_and_length valid (notBit (nonemptyFlag raw))
      cases a <;> cases b <;> simp only [Bool.false_eq_true,if_true,if_false] <;>
        refine ⟨_,_,_,_,_,rfl,?_⟩ <;>
        simp only [List.length_nil,List.length_cons,List.length_append,pair_length,hv,hz] <;> omega

 theorem sat_cnf_iterate_shape (k : ℕ) (rest raw clause formula valid : List Bool) :
    ∃ r u c f v : List Bool,
      (satCNFParseStep^[k]) (satCNFPack rest raw clause formula valid)=satCNFPack r u c f v ∧
      2*r.length+32*u.length+4*c.length+2*f.length+v.length+8 ≤
        2*rest.length+32*raw.length+4*clause.length+2*formula.length+valid.length+8+40*k := by
  induction k with
  | zero => exact ⟨rest,raw,clause,formula,valid,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,u,c,f,v,he,hb⟩ := ih
    obtain ⟨r',u',c',f',v',hs,hl⟩ := sat_cnf_step_shape r u c f v
    refine ⟨r',u',c',f',v',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

 theorem sat_cnf_parse_clock_length (clock input : List Bool) :
    ((satCNFParseStep^[clock.length]) (satCNFPack input [] [] [] [true])).length ≤
      2*input.length+9+40*clock.length := by
  obtain ⟨r,u,c,f,v,he,hb⟩ := sat_cnf_iterate_shape clock.length input [] [] [] [true]
  rw [he,sat_cnf_pack_length]
  simp only [List.length_nil,List.length_cons] at hb
  omega

#print axioms sat_cnf_parse_clock_length
end IV04.Paper.Computational
