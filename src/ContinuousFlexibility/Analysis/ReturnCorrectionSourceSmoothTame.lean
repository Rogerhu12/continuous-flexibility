module

public import ContinuousFlexibility.Analysis.ReturnCorrectionSourceNormBounds
public import ContinuousFlexibility.Analysis.SourceLocalJetAssembly

/-!
# The source-valued tame tower of the actual symmetric divergence

The coefficient assumptions concern actual material derivatives of one
multilinear coefficient family. Physical membership, local norm bounds,
weighted parameter derivatives, second-variation envelopes and source
compatibility are all supplied by the preceding calculus. The result
uses the original projective source topology and its actual grading.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {U : Set E}

theorem smoothTameOn_symmetricSource_of_coefficient_jets
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hU : IsOpen U) (hc : Convex ℝ U)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ (HeightPair S))
    (hpcont : ∀ s, Continuous (p s)) (hqcont : ∀ s, Continuous (q s))
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasInterpolation p) (hIq : HasInterpolation q)
    (hheight : ∀ s η, physicalNorm T (3 / 4 : ℝ) s
      ((S.height (3 / 4 : ℝ)).decode η.1) ≤ q s η)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (hcoeff : LocalCoefficientMaterialTameBounds (T := T) (U := U) p A)
    (hsym : ∀ n x, x ∈ U → ∀ v,
      SymmetricErrorCoefficientSymmetry (A n x v).val)
    (hderiv : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U →
      MixedJetHasDerivAt
        (fun s r => ((A n (x + s • w) v).val (T.radius r.1, r.2)).1)
        (fun r => ((A (n + 1) (x + t • w) (Fin.cons w v)).val
          (T.radius r.1, r.2)).1) t ∧
      MixedJetHasDerivAt
        (fun s r => ((A n (x + s • w) v).val (T.radius r.1, r.2)).2)
        (fun r => ((A (n + 1) (x + t • w) (Fin.cons w v)).val
          (T.radius r.1, r.2)).2) t)
    (f : E × HeightPair S → S.Source)
    (hdecode : ∀ z ∈ U ×ˢ (univ : Set (HeightPair S)),
      physicalSourceDecode S (f z) =
        symmetricDivergenceBilinear hS hT (A 0 z.1 Fin.elim0) z.2) :
    SmoothTameOn (pairGrading p q) S.sourceGrading
      (U ×ˢ (univ : Set (HeightPair S))) f := by
  have hmember := hcoeff.sourceJets_heightMember hS hT hsym
  have henergy := symmetricSourceScalarJets_secondEnvelopes hS hT A
    (hcoeff.lineBounds hT hpcont hp hU)
  have hbound := symmetricSourceScalarJets_local_oneHigh_norm_bound
    hS hT p q hp hq hIp hIq hheight A hcoeff hsym
  have hpaircont (s : ℕ) : Continuous (pairGrading p q s) := by
    change Continuous (fun z : E × HeightPair S => p s z.1 + q s z.2)
    exact ((hpcont s).comp continuous_fst).add ((hqcont s).comp continuous_snd)
  apply smoothTameOn_source_of_local_scalar_jets hS hT (hU.prod isOpen_univ)
    (hc.prod (convex_univ : Convex ℝ (univ : Set (HeightPair S))))
    (pairGrading p q) hpaircont (pairGrading_monotone hp hq) f
    (symmetricSourceScalarJets hS hT A) hmember
  · intro z hz
    exact (symmetricSourceScalarJets_zero hS hT A z).trans (hdecode z hz).symm
  · exact symmetricSourceScalarJets_hasDerivAt_line hS hT A hderiv
  · exact henergy
  · exact hbound

end ContinuousFlexibility.Statements
