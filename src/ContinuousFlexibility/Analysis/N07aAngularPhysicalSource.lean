import ContinuousFlexibility.Analysis.N07aAngularPhysicalMeasure
import ContinuousFlexibility.Analysis.N07aAngularPhysicalPatch
import ContinuousFlexibility.Analysis.N07bAtlasAEPullback

/-!
# The actual physical source is determined by its canonical source classes

The real chart Jacobian and height are nonzero. Equality of canonical
source classes therefore implies equality of physical sources on each
piece. The original a.e. physical cover then gives the same equality on
every inner strip, with no integrability or regularity premise on the
arbitrarily chosen rough representative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K J : CanonicalData S}
  {base loss n : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_physical_piecewise_ae_eq
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    {f g : PolarPoint → ℝ}
    (he : ∀ i, f =ᵐ[n07aPhysicalMeasure S K z i] g) :
    f =ᵐ[canonicalMeasure S J n] g := by
  have hglobal := n07b_ae_physical_of_ae_pieces h04.1 hz hs he
  exact hglobal.filter_mono (ae_mono
    (Measure.restrict_mono (Set.prod_mono hsub subset_rfl) le_rfl))

theorem n07a_canonicalSource_ae_injective_piece
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f g : PolarPoint → ℝ}
    (he : canonicalSource S K z m f =ᵐ[canonicalMeasure S K m] canonicalSource S K z m g) :
    f =ᵐ[n07aPhysicalMeasure S K z m] g :=
  (n07b_canonicalSource_ae_iff h04.1 hz hs m f g).mp he

/-- The source in the original weak relation agrees with the prescribed
physical source whenever they encode the same actual canonical sequence. -/
theorem n07a_sourceRepresentation_local_unique
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    {F : CanonicalSequence S K} {f g : PolarPoint → ℝ}
    (hf : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f)
    (hg : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] canonicalSource S K z m g) :
    f =ᵐ[canonicalMeasure S J n] g :=
  n07a_physical_piecewise_ae_eq h04 hz hs hsub
    (fun m => n07a_canonicalSource_ae_injective_piece h04 hz hs m ((hf m).symm.trans (hg m)))

end ContinuousFlexibility.Analysis
