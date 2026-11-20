module

public import NLA.RA08.PaperNuclearCounterexampleDefinitions
public import NLA.RA08.PaperNuclearParameters
public import NLA.RA08.PaperNuclearTruncation
public import NLA.RA08.PaperNuclearLiftTrace
public import NLA.RA08.PaperNuclearDivergence

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

theorem paper_nuclear_counterexample (C ε₀ : ℝ) (hC : 0 ≤ C) (hε : 0 < ε₀) :
    NuclearTransferFailure C ε₀ := by
  obtain ⟨η,hη0,hη1,hgap⟩ := nuclear_choose_eta ε₀ hε
  obtain ⟨m,hm,hD⟩ := nuclearDerivative_unbounded C
  obtain ⟨K,hK,hKt⟩ := nuclearLiftOutput_lower m η hη0.le hη1.le
  obtain ⟨t,ht,htq,hparams⟩ := nuclear_small_time η
    (nuclearNorm (nuclearDerivative m)) K C ε₀ hη0 hη1 hK hC hε hgap hD
  obtain ⟨d⟩ := nuclearLift_ordered_exists m η t hη1 ht
  let a := nuclearLiftSmallest m η t
  have ha : 0 < a := nuclearLiftSmallest_pos m η t hη1 ht
  have hlow : nuclearLiftTailLower η t ≤ a :=
    nuclearLiftSmallest_lower m hm η t hη0.le hη1.le ht.le htq
  have hupp : a ≤ (1-η)*t := nuclearLiftSmallest_upper m η t hη1.le
  obtain ⟨he0,he1,hein,hout⟩ := hparams a ha hlow hupp
  refine ⟨m+m+1,m+m,m+m,nuclearLiftA m η t,nuclearLiftSketch m η,d,t/a-1,
    nuclearLiftA_posDef m η t hη1 ht,nuclearLiftSketch_injective m η,?_,he0,he1,?_,?_⟩
  · rw [nuclearLift_nystrom m η t hη1,nuclearLiftBase_rank]
  · rw [nuclearLift_nystrom m η t hη1,
      nuclearLift_residual_nuclearNorm m hm η t hη0.le hη1.le ht.le,
      nuclearLift_truncation_tail m η t d]
    exact hein
  · rw [nuclearLift_nystrom m η t hη1,
      nuclearLift_clipping_tail m η t hη0.le hη1.le ht.le htq d]
    exact hout.trans_le (hKt t ht.le)

#print axioms paper_nuclear_counterexample
end NLA.RA08.Paper
