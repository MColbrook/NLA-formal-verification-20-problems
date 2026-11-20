module

public import NLA.MD06.JointSupportCounts.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadSupportEnumeration
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06JointSupportCounts

abbrev SupportedBadDatum (n : ℕ) (S : Finset (Fin n)) :=
  {z : BadDatum n // VertexSupport (BadPattern z) ⊆ S}

abbrev SupportedJointDatum (n q : ℕ) (S : Finset (Fin n)) :=
  {f : JointDatum n q // VertexSupport (JointPattern f) ⊆ S}

abbrev BadCode {n : ℕ} (S : Finset (Fin n)) :=
  (↥S × OrderedLocalPair) ⊕
    (↥S × ↥S × OrderedLocalPair × OrderedLocalPair × Bool)

end Reference.MD06BadSupportEnumeration
