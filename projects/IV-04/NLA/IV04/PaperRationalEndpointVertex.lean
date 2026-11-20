module

public import NLA.IV04.PaperRationalEndpointVertexDefinitions
public import NLA.IV04.PaperMatrixDeterminantVerifierSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem selected_endpoint_words_scaled (D : ℕ) (rows : List (List Bool × List Bool))
    (pairs : List (ℚ × ℚ)) (choices : List Bool)
    (hrows : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(D : ℚ),row.2*(D : ℚ)))) :
    (selectedEndpointWords rows choices).map (fun word => (signedWordValue word : ℚ))=
      (selectedRationalEndpoints pairs choices).map (fun value => value*(D : ℚ)) := by
  induction rows generalizing pairs choices with
  | nil => cases pairs <;> simp_all [selectedEndpointWords,selectedRationalEndpoints]
  | cons row rows ih =>
    obtain ⟨lower,upper⟩ := row
    cases pairs with
    | nil => simp at hrows
    | cons pair pairs =>
      obtain ⟨a,b⟩ := pair
      have hh := (List.cons.inj hrows).1
      have ht := (List.cons.inj hrows).2
      simp only [selectedEndpointWords,selectedRationalEndpoints,List.map_cons]
      apply congrArg₂ List.cons
      · by_cases h : choices.headD false
        · simpa only [if_pos h] using congrArg Prod.snd hh
        · simpa only [if_neg h] using congrArg Prod.fst hh
      · exact ih pairs choices.tail ht

theorem dense_word_selected_rational_matrix (n D : ℕ) (rows : List (List Bool × List Bool))
    (pairs : List (ℚ × ℚ)) (choices : List Bool) (hD : 0<D)
    (hrows : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(D : ℚ),row.2*(D : ℚ)))) :
    denseWordRationalMatrix n D (selectedEndpointWords rows choices)=rationalEndpointVertex n pairs choices := by
  have hDn : (D : ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hs := selected_endpoint_words_scaled D rows pairs choices hrows
  ext i j
  apply (div_eq_iff hDn).mpr
  have h := congrArg (fun values : List ℚ => values.getD (i.val*n+j.val) 0) hs
  have hz : (signedWordValue ([] : List Bool) : ℚ)=0 := rfl
  have hmap {α β : Type} (values : List α) (fallback : α) (f : α → β) (index : ℕ) :
      (values.map f).getD index (f fallback) = f (values.getD index fallback) := by
    simp [List.getD]
  have hw := hmap (selectedEndpointWords rows choices) [] (fun word => (signedWordValue word : ℚ)) (i.val*n+j.val)
  have hr := hmap (selectedRationalEndpoints pairs choices) 0 (fun value => value*(D : ℚ)) (i.val*n+j.val)
  simp only [hz] at hw
  simp only [zero_mul] at hr
  rw [hw,hr] at h
  exact h

theorem dense_row_coordinate_unique (n i j a b : ℕ) (hpos : 0<n) (hj : j<n) (hb : b<n)
    (he : i*n+j=a*n+b) : i=a ∧ j=b := by
  have hd := congrArg (fun k => k/n) he
  have hm := congrArg (fun k => k%n) he
  have hdi : (i*n+j)/n=i := by
    rw [Nat.mul_comm i n,Nat.add_comm,Nat.add_mul_div_left _ _ hpos,Nat.div_eq_of_lt hj,Nat.zero_add]
  have hda : (a*n+b)/n=a := by
    rw [Nat.mul_comm a n,Nat.add_comm,Nat.add_mul_div_left _ _ hpos,Nat.div_eq_of_lt hb,Nat.zero_add]
  have hmj : (i*n+j)%n=j := by
    rw [Nat.mul_comm i n,Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj]
  have hmb : (a*n+b)%n=b := by
    rw [Nat.mul_comm a n,Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hb]
  exact ⟨by simpa only [hdi,hda] using hd,by simpa only [hmj,hmb] using hm⟩

theorem dense_row_cursor_successor (n i j : ℕ) (hj : j<n) :
    (if n≤j+1 then i+1 else i)*n+(if n≤j+1 then 0 else j+1)=i*n+j+1 ∧
      (if n≤j+1 then 0 else j+1)<n := by
  by_cases he : n≤j+1
  · have h : j+1=n := by omega
    simp only [if_pos he]
    constructor
    · rw [Nat.add_zero,Nat.add_mul,Nat.one_mul,← h];omega
    · omega
  · simp only [if_neg he]
    exact ⟨by omega,by omega⟩

theorem rational_dense_selection_offband_at (n i j : ℕ) (pairs : List (ℚ × ℚ))
    (choices : List Bool) (hpos : 0<n) (hj : j<n) (hAll : rationalDenseEndpointAll n i j pairs)
    (a b k : ℕ) (hb : b<n) (haddr : i*n+j+k=a*n+b)
    (hoff : a+1<b ∨ b+1<a) : (selectedRationalEndpoints pairs choices).getD k 0=0 := by
  induction pairs generalizing i j k choices with
  | nil => simp [selectedRationalEndpoints]
  | cons pair pairs ih =>
    obtain ⟨lower,upper⟩ := pair
    change ((i ≤ j+1 ∧ j ≤ i+1) ∨ (lower=0 ∧ upper=0)) ∧ _ at hAll
    cases k with
    | zero =>
      have he : i*n+j=a*n+b := by simpa using haddr
      obtain ⟨hi,hj'⟩ := dense_row_coordinate_unique n i j a b hpos hj hb he
      have hz : lower=0 ∧ upper=0 := hAll.1.resolve_left (by omega)
      simp [selectedRationalEndpoints,hz.1,hz.2]
    | succ k =>
      have hs := dense_row_cursor_successor n i j hj
      have ha : (if n≤j+1 then i+1 else i)*n+(if n≤j+1 then 0 else j+1)+k=a*n+b := by
        rw [hs.1];omega
      simpa [selectedRationalEndpoints] using
        ih (if n≤j+1 then i+1 else i) (if n≤j+1 then 0 else j+1) choices.tail hs.2 hAll.2 k ha

theorem rational_endpoint_vertex_tridiagonal (n : ℕ) (pairs : List (ℚ × ℚ)) (choices : List Bool)
    (hAll : rationalDenseEndpointAll n 0 0 pairs) : RationalTridiagonal (rationalEndpointVertex n pairs choices) := by
  intro i j hoff
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  exact rational_dense_selection_offband_at n 0 0 pairs choices hn hn hAll i.val j.val
    (i.val*n+j.val) j.isLt (by simp) hoff

theorem selected_rational_endpoints_getD (pairs : List (ℚ × ℚ)) (choices : List Bool) (k : ℕ) :
    (selectedRationalEndpoints pairs choices).getD k 0=
      if choices.getD k false then (pairs.getD k (0,0)).2 else (pairs.getD k (0,0)).1 := by
  induction pairs generalizing choices k with
  | nil =>
    simp only [selectedRationalEndpoints,List.getD_nil]
    split_ifs <;> rfl
  | cons pair pairs ih =>
    obtain ⟨lower,upper⟩ := pair
    cases k with
    | zero => cases choices <;> rfl
    | succ k =>
      cases choices with
      | nil => simpa [selectedRationalEndpoints] using ih [] k
      | cons b choices => simpa [selectedRationalEndpoints] using ih choices k

theorem rational_endpoint_vertex_bounds (n : ℕ) (pairs : List (ℚ × ℚ)) (choices : List Bool)
    (horder : ∀ row ∈ pairs, row.1 ≤ row.2) (i j : Fin n) :
    (pairs.getD (i.val*n+j.val) (0,0)).1 ≤ rationalEndpointVertex n pairs choices i j ∧
      rationalEndpointVertex n pairs choices i j ≤ (pairs.getD (i.val*n+j.val) (0,0)).2 := by
  have ho : (pairs.getD (i.val*n+j.val) (0,0)).1 ≤ (pairs.getD (i.val*n+j.val) (0,0)).2 := by
    by_cases hk : i.val*n+j.val < pairs.length
    · rw [← List.getElem_eq_getD (l := pairs) (h := hk) (0,0)]
      exact horder _ (List.getElem_mem _)
    · simp [List.getD, hk]
  rw [rationalEndpointVertex,selected_rational_endpoints_getD]
  split_ifs
  · exact ⟨ho,le_rfl⟩
  · exact ⟨le_rfl,ho⟩

#print axioms rational_endpoint_vertex_tridiagonal
end IV04.Paper.Computational