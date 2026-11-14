module

public import ContinuousFlexibility.Analysis.N05CanonicalPhysicalRepresentatives
public import ContinuousFlexibility.Analysis.N05PhysicalGraphUniqueness
public import ContinuousFlexibility.Analysis.N05ReferenceNormalization

/-!
# Identification of the physical representatives of a canonical graph

The literal graph gives periodicity of the source after subtracting its
normalized auxiliary column. The column is itself periodic, so equality of
the canonical source representatives determines the full physical source.
Compatibility and the fixed physical inverse then identify the auxiliary
scalar, metric scalar and physical height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory

theorem n05_augmentedSource_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) {γ M a : ℝ} {f : PolarPoint → ℝ}
    (hf : SourceMember D γ M
      ((fun p => f p - a * (S.height (3 / 4 : ℝ)).decode S.psi p), 0)) :
    Function.Periodic f (0, Real.pi) := by
  have hψ : Function.Periodic ((S.height (3 / 4 : ℝ)).decode S.psi)
      (0, Real.pi) := ((hS.1 _).2.2.2.1 S.psi).2.2.1
  intro p
  have hp := hf.2.2.1 p
  change f (p + (0, Real.pi)) -
      a * (S.height (3 / 4 : ℝ)).decode S.psi (p + (0, Real.pi)) =
    f p - a * (S.height (3 / 4 : ℝ)).decode S.psi p at hp
  rw [hψ p] at hp
  linarith

/-- Both actual physical representations of the same canonical source have
the same source, auxiliary scalar, metric scalar and height equivalence class.
The left constant is subsequently determined by the canonical endpoint class. -/
theorem n05_canonicalGraph_physical_representatives_unique
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε γ M0 M1 : ℝ}
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (h04 : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M0 M1 G)
    {U V : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {η ζ f g : PolarPoint → ℝ}
    (hU : HasCanonicalRepresentation D S C K (C.referenceState, 0) U F η f)
    (hV : HasCanonicalRepresentation D S C K (C.referenceState, 0) V F ζ g)
    (hη : ReferenceGraph D γ M0 M1 (η, U.2.2.1)
      ((fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0))
    (hζ : ReferenceGraph D γ M0 M1 (ζ, V.2.2.1)
      ((fun p => g p - V.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0)) :
    (f =ᵐ[radialPhysicalMeasure D] g) ∧ U.2.2.2 = V.2.2.2 ∧
      U.2.2.1 = V.2.2.1 ∧ (η =ᵐ[radialPhysicalMeasure D] ζ) := by
  have hfg := n05_referenceCanonicalSource_ae_physical h04 hcoordinates
    (n05_augmentedSource_periodic hS hη.2.1)
    (n05_augmentedSource_periodic hS hζ.2.1)
    (fun m => (hU.2 m).symm.trans (hV.2 m))
  have hunique := n05_augmentedReferenceGraph_unique_source_ae hD hγ hG
    (n05_physicalSpaces_normalizer_referenceIntegral hS) hfg hη hζ
  exact ⟨hfg, hunique.1, hunique.2.1, hunique.2.2⟩

end ContinuousFlexibility.Statements
