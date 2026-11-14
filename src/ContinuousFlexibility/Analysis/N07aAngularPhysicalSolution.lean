module

public import ContinuousFlexibility.Analysis.N07aAngularActualPhysicalRegularity
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalEncoding
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalEven
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalClassical
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalAEPairing

/-!
# The same perturbed canonical solution has the actual classical physical field

The genuine N06 relation supplies the original rough representative and
its normalization. All angular and normal regularity is established on
that same L² class. The final field keeps its canonical coordinates, its
physical row, its evenness, and the actual corrected differential equation.
No prior physical trace regularity is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_perturbedCanonical_smooth_solution
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
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : PerturbedCanonicalRelation D S C K L (liftSectorParameter S C z) U F)
    (hU : ∀ m k, N07aCanonicalNormalRegular S K m (U.1 m) k)
    (hreference : N07aReferenceGraphRepresentation D S C K U)
    (hEven : ∀ m, n07aAngularReflection m (U.1 m) = U.1 m)
    (f₀ : S.Source)
    (hF : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode f₀.val))
    (hnormal : N07aActualNormalEquation D S C L K z U f₀
      (fun m => n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
        ⟨U.1 m, hU m⟩)) :
    ∃ v : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ v (annularOpen D) ∧
      Function.Periodic v (0, Real.pi) ∧ (∀ r θ, v (r, -θ) = v (r, θ)) ∧
      (∀ p, p ∉ annularOpen D → v p = 0) ∧
      HasCanonicalRepresentation D S C K (liftSectorParameter S C z) U F v
        ((S.height (3 / 4 : ℝ)).decode f₀.val) ∧
      referenceRow D v = 0 ∧
      ∀ p ∈ annularOpen D,
        divergenceOperator (L.coefficients (liftSectorParameter S C z)) v p +
          U.2.2.1 * nuColumnField D S C (liftSectorParameter S C z) p +
          U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p =
            (S.height (3 / 4 : ℝ)).decode f₀.val p := by
  obtain ⟨η, f, hrep, hηp, hfp, hrow, heq⟩ := hrel
  obtain ⟨v, hv, hvp, hve, hvzero⟩ := n07a_currentWeak_smoothPhysical
    hD hT hS h01 h03 h04 href hcur hcanonical hborder z hz hz' hs
    hrep hU hreference f₀ hF hnormal hηp hfp heq
  have hrepv := n07a_canonicalRepresentation_replace_height h04 hz' hs hrep hve
  have hveven := n07a_canonicalRepresentation_smooth_even hS h04 hz' hs
    hrepv hU hEven hv hvp hvzero
  have hfe : f =ᵐ[canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0]
      (S.height (3 / 4 : ℝ)).decode f₀.val :=
    n07a_sourceRepresentation_local_unique h04 hz' hs Subset.rfl hrep.2 hF
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  refine ⟨v, hv, hvp, hveven, hvzero, ⟨hrepv.1, hF⟩,
    (n07a_referenceRow_congr_ae hab hvp hηp hve).trans hrow, ?_⟩
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
  exact n07a_physicalWeak_smooth_classical hab (L.coefficients x)
    ⟨ha, hspace.2.1, hspace.2.2.1⟩
    (by
      rintro ⟨s, θ⟩ hp
      refine ⟨hap (s, θ) hp, ?_, ?_⟩
      · simpa only [Prod.mk_add_mk, add_zero] using
          hspace.2.2.2.1 s hp.1 θ
      · simpa only [Prod.mk_add_mk, add_zero] using
          hspace.2.2.2.2 s hp.1 θ)
    η f v ((S.height (3 / 4 : ℝ)).decode f₀.val)
    (nuColumnField D S C x) ((S.height (3 / 4 : ℝ)).decode S.psi)
    U.2.2.1 U.2.2.2 hηp hfp hv hf₀.1
    (n07a_nuColumnField_contDiffOn hS hT h01 hz' hs) hψ.1 hvp
    hf₀.2.2.1 (n07a_nuColumnField_periodic hS x) hψ.2.2.1 hve hfe heq

end ContinuousFlexibility.Analysis
