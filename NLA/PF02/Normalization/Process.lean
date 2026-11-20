module

public import NLA.PF02.Normalization.Continuity
public import NLA.PF02.Normalization.OrderBounds
public import NLA.PF02.Normalization.CompactDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem continuousOn_normalization_pair (p q k : ℕ) :
    ContinuousOn (fun F : FactorPair p q k => (normalizedRow F.1, normalizedColumn F.1 F.2))
      {F | (rowSum F.1).PosDef} := by
  have hr : ContinuousOn (fun F : FactorPair p q k => normalizedRow F.1)
      {F | (rowSum F.1).PosDef} := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuousOn_normalized_row p k i).comp continuous_fst.continuousOn
      (fun F hF => hF)
  have hc : ContinuousOn (fun F : FactorPair p q k => normalizedColumn F.1 F.2)
      {F | (rowSum F.1).PosDef} := by
    apply continuousOn_pi.mpr
    exact fun j => continuousOn_normalized_column p q k j
  exact hr.prodMk hc

#print axioms continuousOn_normalization_pair
end Reference.PF02Normalization
