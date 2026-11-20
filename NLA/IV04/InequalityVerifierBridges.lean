module

public import NLA.IV04.InequalityVerifierDefinitions
public import NLA.IV04.InequalityIntegerBridge
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational
namespace IV04.Paper.InequalityVerifier

private theorem xorSuffix_frozen : EqualityFlags.xorSuffix = Cobham.xorSuffix := by
  funext a b
  induction a with
  | nil => rfl
  | cons bit tail ih => cases bit <;> simp only [EqualityFlags.xorSuffix, Cobham.xorSuffix, ih]

private theorem allZeroFlag_frozen : EqualityFlags.allZeroFlag = Cobham.allZeroFlag := by
  funext a
  induction a with
  | nil => rfl
  | cons bit tail ih => cases bit <;> simp only [EqualityFlags.allZeroFlag, Cobham.allZeroFlag, ih]

private theorem eqFlag_frozen : EqualityFlags.eqFlag = Cobham.eqFlag := by
  funext
  simp only [EqualityFlags.eqFlag, Cobham.eqFlag, EqualityFlags.lenEqFlag,
    Cobham.lenEqFlag, EqualityFlags.lenLeFlag, Cobham.lenLeFlag,
    xorSuffix_frozen, allZeroFlag_frozen]

theorem signedDotPack_frozen : signedDotPack = IV04.Paper.Computational.signedDotPack := by
  funext
  simp only [signedDotPack, IV04.Paper.Computational.signedDotPack]

theorem signedDotStep_frozen : signedDotStep = IV04.Paper.Computational.signedDotStep := by
  funext
  simp only [signedDotStep, IV04.Paper.Computational.signedDotStep, signedDotPack_frozen]

theorem signedDotState_frozen : signedDotState = IV04.Paper.Computational.signedDotState := by
  funext
  simp only [signedDotState, IV04.Paper.Computational.signedDotState, signedDotPack_frozen, signedDotStep_frozen]

theorem polynomialSignedDot_frozen : polynomialSignedDot = IV04.Paper.Computational.polynomialSignedDot := by
  funext
  simp only [polynomialSignedDot, IV04.Paper.Computational.polynomialSignedDot, signedDotState_frozen]

theorem signedPayloadDot_frozen : signedPayloadDot = IV04.Paper.Computational.signedPayloadDot := by
  funext left right
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a tail ih =>
    cases right with
    | nil => rfl
    | cons p ps => simp only [signedPayloadDot, IV04.Paper.Computational.signedPayloadDot, ih]

theorem payloadSyntaxStep_frozen : payloadSyntaxStep = IV04.Paper.Computational.payloadSyntaxStep := by
  funext
  simp only [payloadSyntaxStep, IV04.Paper.Computational.payloadSyntaxStep, eqFlag_frozen]

theorem payloadSyntaxState_frozen : payloadSyntaxState = IV04.Paper.Computational.payloadSyntaxState := by
  funext
  simp only [payloadSyntaxState, IV04.Paper.Computational.payloadSyntaxState, payloadSyntaxStep_frozen]

theorem payloadSyntaxVerdict_frozen : payloadSyntaxVerdict = IV04.Paper.Computational.payloadSyntaxVerdict := by
  funext
  simp only [payloadSyntaxVerdict, IV04.Paper.Computational.payloadSyntaxVerdict, eqFlag_frozen]

theorem polynomialPayloadSyntax_frozen : polynomialPayloadSyntax = IV04.Paper.Computational.polynomialPayloadSyntax := by
  funext
  simp only [polynomialPayloadSyntax, IV04.Paper.Computational.polynomialPayloadSyntax, payloadSyntaxState_frozen, payloadSyntaxVerdict_frozen]

theorem inequalityRowPack_frozen : inequalityRowPack = IV04.Paper.Computational.inequalityRowPack := by
  funext
  simp only [inequalityRowPack, IV04.Paper.Computational.inequalityRowPack]

theorem inequalityRowCode_frozen : inequalityRowCode = IV04.Paper.Computational.inequalityRowCode := by
  funext
  simp only [inequalityRowCode, IV04.Paper.Computational.inequalityRowCode, inequalityRowPack_frozen]

theorem inequalityRowCoefficients_frozen : inequalityRowCoefficients = IV04.Paper.Computational.inequalityRowCoefficients := by
  funext
  simp only [inequalityRowCoefficients, IV04.Paper.Computational.inequalityRowCoefficients]

theorem inequalityRowBound_frozen : inequalityRowBound = IV04.Paper.Computational.inequalityRowBound := by
  funext
  simp only [inequalityRowBound, IV04.Paper.Computational.inequalityRowBound]

theorem inequalityRowNumerators_frozen : inequalityRowNumerators = IV04.Paper.Computational.inequalityRowNumerators := by
  funext
  simp only [inequalityRowNumerators, IV04.Paper.Computational.inequalityRowNumerators]

theorem inequalityRowDenominator_frozen : inequalityRowDenominator = IV04.Paper.Computational.inequalityRowDenominator := by
  funext
  simp only [inequalityRowDenominator, IV04.Paper.Computational.inequalityRowDenominator]

theorem inequalityRowRepack_frozen : inequalityRowRepack = IV04.Paper.Computational.inequalityRowRepack := by
  funext
  simp only [inequalityRowRepack, IV04.Paper.Computational.inequalityRowRepack, inequalityRowPack_frozen, inequalityRowCoefficients_frozen, inequalityRowBound_frozen, inequalityRowNumerators_frozen, inequalityRowDenominator_frozen]

theorem inequalityRowArithmetic_frozen : inequalityRowArithmetic = IV04.Paper.Computational.inequalityRowArithmetic := by
  funext
  simp only [inequalityRowArithmetic, IV04.Paper.Computational.inequalityRowArithmetic, polynomialSignedDot_frozen, inequalityRowCoefficients_frozen, inequalityRowBound_frozen, inequalityRowNumerators_frozen, inequalityRowDenominator_frozen]

theorem polynomialInequalityRowVerifier_frozen : polynomialInequalityRowVerifier = IV04.Paper.Computational.polynomialInequalityRowVerifier := by
  funext
  simp only [polynomialInequalityRowVerifier, IV04.Paper.Computational.polynomialInequalityRowVerifier, eqFlag_frozen, polynomialPayloadSyntax_frozen, inequalityRowCoefficients_frozen, inequalityRowNumerators_frozen, inequalityRowDenominator_frozen, inequalityRowRepack_frozen, inequalityRowArithmetic_frozen]

theorem inequalityRowAccepts_frozen : inequalityRowAccepts = IV04.Paper.Computational.inequalityRowAccepts := by
  funext
  simp only [inequalityRowAccepts, IV04.Paper.Computational.inequalityRowAccepts, signedPayloadDot_frozen, inequalityRowCode_frozen]

theorem inequalityRowAt_frozen : inequalityRowAt = IV04.Paper.Computational.inequalityRowAt := by
  funext
  simp only [inequalityRowAt, IV04.Paper.Computational.inequalityRowAt, eqFlag_frozen, inequalityRowPack_frozen, polynomialInequalityRowVerifier_frozen]

theorem inequalityRowsPack_frozen : inequalityRowsPack = IV04.Paper.Computational.inequalityRowsPack := by
  funext
  simp only [inequalityRowsPack, IV04.Paper.Computational.inequalityRowsPack]

theorem inequalityRowsStep_frozen : inequalityRowsStep = IV04.Paper.Computational.inequalityRowsStep := by
  funext
  simp only [inequalityRowsStep, IV04.Paper.Computational.inequalityRowsStep, eqFlag_frozen, inequalityRowAt_frozen, inequalityRowsPack_frozen]

theorem inequalityRowsState_frozen : inequalityRowsState = IV04.Paper.Computational.inequalityRowsState := by
  funext
  simp only [inequalityRowsState, IV04.Paper.Computational.inequalityRowsState, inequalityRowsPack_frozen, inequalityRowsStep_frozen]

theorem inequalityRowsVerdict_frozen : inequalityRowsVerdict = IV04.Paper.Computational.inequalityRowsVerdict := by
  funext
  simp only [inequalityRowsVerdict, IV04.Paper.Computational.inequalityRowsVerdict, eqFlag_frozen]

theorem inequalitySystemRepack_frozen : inequalitySystemRepack = IV04.Paper.Computational.inequalitySystemRepack := by
  funext
  simp only [inequalitySystemRepack, IV04.Paper.Computational.inequalitySystemRepack]

theorem polynomialInequalitySystemVerifier_frozen : polynomialInequalitySystemVerifier = IV04.Paper.Computational.polynomialInequalitySystemVerifier := by
  funext
  simp only [polynomialInequalitySystemVerifier, IV04.Paper.Computational.polynomialInequalitySystemVerifier, eqFlag_frozen, polynomialPayloadSyntax_frozen, inequalityRowsState_frozen, inequalityRowsVerdict_frozen, inequalitySystemRepack_frozen]

theorem decodedInequalityRow_frozen : decodedInequalityRow = IV04.Paper.Computational.decodedInequalityRow := by
  funext
  simp only [decodedInequalityRow, IV04.Paper.Computational.decodedInequalityRow, signedPayloadDot_frozen]

theorem inequalitySystemCode_frozen : inequalitySystemCode = IV04.Paper.Computational.inequalitySystemCode := by
  funext
  simp only [inequalitySystemCode, IV04.Paper.Computational.inequalitySystemCode]

theorem inequalitySystemAccepts_frozen : inequalitySystemAccepts = IV04.Paper.Computational.inequalitySystemAccepts := by
  funext
  simp only [inequalitySystemAccepts, IV04.Paper.Computational.inequalitySystemAccepts, decodedInequalityRow_frozen, inequalitySystemCode_frozen]

theorem inequalityTypedSystemCode_frozen : inequalityTypedSystemCode = IV04.Paper.Computational.inequalityTypedSystemCode := by
  funext
  simp only [inequalityTypedSystemCode, IV04.Paper.Computational.inequalityTypedSystemCode, inequalitySystemCode_frozen]

theorem inequalityIntegerWord_frozen : inequalityIntegerWord = IV04.Paper.Computational.inequalityIntegerWord := by
  funext
  simp only [inequalityIntegerWord, IV04.Paper.Computational.inequalityIntegerWord]

theorem inequalityIntegerDot_frozen : inequalityIntegerDot = IV04.Paper.Computational.inequalityIntegerDot := by
  funext left right
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a tail ih =>
    cases right with
    | nil => rfl
    | cons p ps => simp only [inequalityIntegerDot, IV04.Paper.Computational.inequalityIntegerDot, ih]

theorem inequalityIntegerSystemCode_frozen : inequalityIntegerSystemCode = IV04.Paper.Computational.inequalityIntegerSystemCode := by
  funext
  simp only [inequalityIntegerSystemCode, IV04.Paper.Computational.inequalityIntegerSystemCode, inequalityTypedSystemCode_frozen, inequalityIntegerWord_frozen]

#print axioms xorSuffix_frozen
#print axioms allZeroFlag_frozen
#print axioms eqFlag_frozen
#print axioms signedDotPack_frozen
#print axioms signedDotStep_frozen
#print axioms signedDotState_frozen
#print axioms polynomialSignedDot_frozen
#print axioms signedPayloadDot_frozen
#print axioms payloadSyntaxStep_frozen
#print axioms payloadSyntaxState_frozen
#print axioms payloadSyntaxVerdict_frozen
#print axioms polynomialPayloadSyntax_frozen
#print axioms inequalityRowPack_frozen
#print axioms inequalityRowCode_frozen
#print axioms inequalityRowCoefficients_frozen
#print axioms inequalityRowBound_frozen
#print axioms inequalityRowNumerators_frozen
#print axioms inequalityRowDenominator_frozen
#print axioms inequalityRowRepack_frozen
#print axioms inequalityRowArithmetic_frozen
#print axioms polynomialInequalityRowVerifier_frozen
#print axioms inequalityRowAccepts_frozen
#print axioms inequalityRowAt_frozen
#print axioms inequalityRowsPack_frozen
#print axioms inequalityRowsStep_frozen
#print axioms inequalityRowsState_frozen
#print axioms inequalityRowsVerdict_frozen
#print axioms inequalitySystemRepack_frozen
#print axioms polynomialInequalitySystemVerifier_frozen
#print axioms decodedInequalityRow_frozen
#print axioms inequalitySystemCode_frozen
#print axioms inequalitySystemAccepts_frozen
#print axioms inequalityTypedSystemCode_frozen
#print axioms inequalityIntegerWord_frozen
#print axioms inequalityIntegerDot_frozen
#print axioms inequalityIntegerSystemCode_frozen
end IV04.Paper.InequalityVerifier
