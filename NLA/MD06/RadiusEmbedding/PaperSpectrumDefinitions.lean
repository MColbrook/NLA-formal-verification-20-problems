module

public import NLA.MD06.LaplacianSpectralGap.Definitions

@[expose] public section
namespace Reference.MD06RadiusEmbedding
attribute [local instance] Classical.propDecidable
noncomputable def TotalLaplacianGap {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  if hn : 2 ≤ n then Reference.MD06Spectral.LaplacianGap G hn else 0
end Reference.MD06RadiusEmbedding
