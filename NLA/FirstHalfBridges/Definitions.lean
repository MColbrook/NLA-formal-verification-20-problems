module

public import NLA.MF07.Definitions
public import NLA.MF05.RealGeometry.Definitions
public import NLA.MF12.PaperDefinitions
public import NLA.MF12.PaperDyadicDefinitions
public import NLA.RA02.Definitions
public import NLA.RA08.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace RootFirstHalfBridges

def skewNorm {𝕜 : Type*} [inst : RCLike 𝕜] (x : EuclideanSpace 𝕜 (Fin 2)) : ℝ :=
  ‖x 0+x 1‖+(1/2:ℝ)*‖x 1‖

def coordinateProjection {𝕜 : Type*} [inst : RCLike 𝕜]
    (x : EuclideanSpace 𝕜 (Fin 2)) : EuclideanSpace 𝕜 (Fin 2) :=
  WithLp.toLp 2 ![x 0,0]

def projectionWitness {𝕜 : Type*} [inst : RCLike 𝕜] : EuclideanSpace 𝕜 (Fin 2) :=
  WithLp.toLp 2 ![1,-1]

end RootFirstHalfBridges
