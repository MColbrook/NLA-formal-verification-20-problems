module

public import NLA.MI22.Commuting.Proof
public import NLA.MI22.Commuting.Numerical

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
open Matrix
namespace NLA.MI22.Commuting.Interface
open NLA.MI22.Paper

theorem commuting_weighted_mean {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : Commute A B) (t : ℝ) :
    weightedMean A B t = spectralPower A (1-t) * spectralPower B t := by
  exact NLA.MI22.Commuting.commuting_weighted_mean A B hA hB hAB t

theorem commuting_left_product {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : Commute A B) (t : ℝ) : leftProduct A B t = A * B := by
  exact NLA.MI22.Commuting.commuting_left_product A B hA hB hAB t

theorem literal_principal_minors :
    paperB 0 0 = 17 ∧
      (paperB.submatrix (fun i : Fin 2 => i.castLE (by decide)) (fun i : Fin 2 => i.castLE (by decide))).det = 278529 ∧
      paperB.det = 4096 := by
  exact NLA.MI22.Commuting.literal_principal_minors

theorem literal_root_coefficient :
    (1/8:ℝ) * ((2:ℝ)^(-10:ℝ))^(-7/8:ℝ) = (2:ℝ)^(23/4:ℝ) ∧
      (2:ℝ)^(23/4:ℝ) < 64 := by
  exact NLA.MI22.Commuting.literal_root_coefficient

theorem literal_error_constant :
    (32*16*(64*(10:ℝ)^(-8:ℤ))*(4^7+8*7*4^6)) = 6291456/78125 ∧
      (6291456/78125:ℝ) < 100 := by
  exact NLA.MI22.Commuting.literal_error_constant

theorem literal_matrix_product :
    witnessA * paperB = !![(4352:ℂ), -1024, 0; -1/64, 16385/256, -32; 0, -8192, 4096] := by
  exact NLA.MI22.Commuting.literal_matrix_product

end NLA.MI22.Commuting.Interface
