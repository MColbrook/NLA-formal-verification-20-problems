module

public import NLA.IV04.InequalityIntegerBridge
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational
namespace IV04.Paper.InequalityCertificate

def inequalityIntegerCertificateCode (numerators : List ℤ) (denominator : ℕ) : List Bool :=
  pair (payloadListCode (numerators.map inequalityIntegerWord)) denominator.bits

theorem natural_size_of_pow_bound (q K : ℕ) (hq : q≤2^K) : q.size≤K+1 := by
  apply Nat.size_le.mpr
  have hpow : (2 : ℕ)^K<2^(K+1) := by
    rw [pow_succ]
    have hpos : 0<(2 : ℕ)^K := pow_pos (by omega) K
    omega
  exact lt_of_le_of_lt hq hpow

theorem integer_word_length_of_pow_bound (z : ℤ) (K : ℕ)
    (hz : |z|≤((2^K : ℕ) : ℤ)) : (inequalityIntegerWord z).length≤K+2 := by
  rw [inequality_integer_word_length]
  have hnat : z.natAbs≤2^K := by
    have hcast : (z.natAbs : ℤ)≤((2^K : ℕ) : ℤ) := by
      simpa only [Int.natCast_natAbs] using hz
    exact_mod_cast hcast
  have h := natural_size_of_pow_bound z.natAbs K hnat
  omega

theorem payload_length_sum_bound (words : List (List Bool)) (B : ℕ)
    (hwords : ∀ word ∈ words, word.length≤B) :
    (words.map List.length).sum≤words.length*B := by
  induction words with
  | nil => simp
  | cons word rest ih =>
    have hw := hwords word (by simp)
    have hr : ∀ w ∈ rest, w.length≤B := fun w h => hwords w (by simp [h])
    have hi := ih hr
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

theorem integer_certificate_length_bound (numerators : List ℤ) (denominator K : ℕ)
    (hp : ∀ z ∈ numerators, |z|≤((2^K : ℕ) : ℤ)) (hd : denominator≤2^K) :
    (inequalityIntegerCertificateCode numerators denominator).length≤
      (4*numerators.length+1)*(K+3) := by
  have hwords : ∀ word ∈ numerators.map inequalityIntegerWord, word.length≤K+2 := by
    intro word hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    exact integer_word_length_of_pow_bound z K (hp z hz)
  have hsum := payload_length_sum_bound (numerators.map inequalityIntegerWord) (K+2) hwords
  simp only [List.length_map] at hsum
  have hsize := natural_size_of_pow_bound denominator K hd
  rw [inequalityIntegerCertificateCode,pair_length,inequality_payload_list_code_length,
    Nat.size_eq_bits_len]
  simp only [List.length_map]
  nlinarith

#print axioms natural_size_of_pow_bound
#print axioms integer_word_length_of_pow_bound
#print axioms payload_length_sum_bound
#print axioms integer_certificate_length_bound
end IV04.Paper.InequalityCertificate
