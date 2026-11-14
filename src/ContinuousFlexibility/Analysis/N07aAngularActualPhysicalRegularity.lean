module

public import ContinuousFlexibility.Analysis.N07aAngularPhysicalAngular
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalSource
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalLocalRegularity
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalGluing
public import ContinuousFlexibility.Analysis.N07aAngularNuRegularity
public import ContinuousFlexibility.Analysis.N07aLeadingRegularity

/-!
# The actual nonlinear weak solution is smooth on the physical annulus

The input is the same rough representative from the genuine corrected
weak equation. Its canonical all-order jets supply physical angular jets;
actual N01/N03 coefficients, the real distinguished column and the given
physical source then recover all normal jets on compact inner strips.
The final representative is glued across every root and cut without
using any pre-existing smooth traces of the unknown.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K J : CanonicalData S}
  {base loss n : ℕ} {ε : ℝ}

/-- Adding the genuine smooth left column returns the original unknown
from its canonical height remainder, in the same local measure. -/
theorem n07a_currentWeak_localAngular
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hborder : RadialTrueBorder D)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (liftSectorParameter S C z) U F η f)
    (hU : ∀ m k, N07aCanonicalNormalRegular S K m (U.1 m) k)
    (hreference : N07aReferenceGraphRepresentation D S C K U)
    (f₀ : S.Source)
    (hnormal : N07aActualNormalEquation D S C L K z U f₀
      (fun m => n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
        ⟨U.1 m, hU m⟩))
    (hinner : Icc (J.left n) (J.right n) ⊆ Ioo D.a D.b) :
    ∃ u : CanonicalL2 S J n, N07aCanonicalNormalRegular S J n u 0 ∧
      (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] η := by
  obtain ⟨u, hu, hue⟩ := n07a_representation_local_angularRegular hD hT hS h01 h04 href hcur
    hcanonical hborder z hz hz' hs hrep hU hreference f₀ hnormal hinner
  let χ : N07aCanonicalOpenCoefficient S J n := n07aInteriorCoefficient
    ((contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)).contDiffOn)
    (f := fun p : PolarPoint => U.2.1 * S.chiLeft p.1)
    (fun p _ => by simp only [Prod.fst_add, add_zero]) hinner
  refine ⟨u + χ.toLp, hu.add (χ.toLp_normalRegular 0), ?_⟩
  filter_upwards [Lp.coeFn_add u χ.toLp, hue, χ.toLp_ae] with p hp hpu hpχ
  simp only [Pi.add_apply, hpu, hpχ] at hp
  exact hp.trans (by dsimp only [χ, n07aInteriorCoefficient]; ring)

/-- Every regularity premise on the physical coefficients and columns
comes from the actual construction; none is a premise about the solution. -/
theorem n07a_currentWeak_smoothPhysical
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hborder : RadialTrueBorder D)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (liftSectorParameter S C z) U F η f)
    (hU : ∀ m k, N07aCanonicalNormalRegular S K m (U.1 m) k)
    (hreference : N07aReferenceGraphRepresentation D S C K U)
    (f₀ : S.Source)
    (hF : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode f₀.val))
    (hnormal : N07aActualNormalEquation D S C L K z U f₀
      (fun m => n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
        ⟨U.1 m, hU m⟩))
    (hηp : Function.Periodic η (0, Real.pi))
    (hfp : Function.Periodic f (0, Real.pi))
    (heq : ∀ φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ => η (r, θ) *
        divergenceOperator (L.coefficients (liftSectorParameter S C z)) φ (r, θ))) +
      U.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C (liftSectorParameter S C z) (r, θ) * φ (r, θ))) +
      U.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) :
    ∃ v : PolarPoint → ℝ, ContDiffOn ℝ ∞ v (annularOpen D) ∧
      Function.Periodic v (0, Real.pi) ∧
      v =ᵐ[canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0] η ∧
      ∀ p, p ∉ annularOpen D → v p = 0 := by
  let x := liftSectorParameter S C z
  have hspace := hcanonical.physicalCoefficients x hz' hs
  have ha := hspace.1
  have hap : ∀ p ∈ annularOpen D,
      (L.coefficients x).a (p + (0, Real.pi)) = (L.coefficients x).a p := by
    intro p _
    rw [h03.1 x hz' hs, h03.1 x hz' hs]
    exact (n07a_originalCoefficients_periodic hS x).1 p
  have hf₀ := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f₀.val)
  have hψ := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi)
  apply n07a_exists_smooth_physicalRepresentative (K := K) η
  intro l r hlr hinner
  apply n07a_physical_equation_innerSmooth (hD.choose_spec.1.2.1.le) (L.coefficients x)
    ⟨ha, hspace.2.1, hspace.2.2.1⟩
    (by
      rintro ⟨s, θ⟩ hp
      refine ⟨hap (s, θ) hp, ?_, ?_⟩
      · simpa only [Prod.mk_add_mk, add_zero] using
          hspace.2.2.2.1 s hp.1 θ
      · simpa only [Prod.mk_add_mk, add_zero] using
          hspace.2.2.2.2 s hp.1 θ)
    (fun p hp => n07a_correctedLeadingCoefficient_pos h01 h03 hz' hs hp)
    η f ((S.height (3 / 4 : ℝ)).decode f₀.val)
    (nuColumnField D S C x) ((S.height (3 / 4 : ℝ)).decode S.psi)
    U.2.2.1 U.2.2.2 hηp hfp hf₀.1
    (n07a_nuColumnField_contDiffOn hS hT h01 hz' hs) hψ.1
    hf₀.2.2.1 (n07a_nuColumnField_periodic hS x) hψ.2.2.1
  · intro a b _ hab
    exact n07a_currentWeak_localAngular hD hT hS h01 h04 href hcur hcanonical hborder
      z hz hz' hs hrep hU hreference f₀ hnormal hab
  · intro a b _ hab
    exact n07a_sourceRepresentation_local_unique h04 hz' hs
      (fun p hp => hab (Ioo_subset_Icc_self hp)) hrep.2 hF
  · exact heq
  · exact hlr
  · exact hinner

end ContinuousFlexibility.Analysis
