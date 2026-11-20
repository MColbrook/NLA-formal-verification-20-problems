module

public import NLA.MD06.RadiusEmbedding.PaperSpectrumDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MainAssembly
open Reference.MD06Actual
open scoped BigOperators

def StableNonsynchronized {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ theta : Phase n, (∀ i,Gradient G theta i=0) ∧
    IsLocalMin (Energy G) theta ∧ ¬Synchronized theta ∧
    (∀ i j,G.Adj i j → (1/32 : ℝ)<Real.Angle.cos (theta i-theta j)) ∧
    ∀ z : Fin n→ℝ,(∑ i,z i)=0 →
      (1/320 : ℝ)*(∑ i,(z i)^2)≤HessianQuadratic G theta z

def EveryLocalMinimumSynchronized {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ theta : Phase n,IsLocalMin (Energy G) theta → Synchronized theta
end Reference.MD06MainAssembly
