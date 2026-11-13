import ContinuousFlexibility.Analysis.N04PrincipalNegativePotential

/-!
# Coordinate-partial form of the negative potential

This is the same negative potential identity in the operators used by
the paired jet calculus. Spatial smoothness comes from the qualitative
chart and height certificate on the actual canonical open piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff

theorem n04PrincipalNegative_secondPartials
    {Ω : Set PolarPoint} (hΩ : IsOpen Ω) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω) {q : PolarPoint} (hq : q ∈ Ω) :
    radialPartial (radialPartial v) q = mixedDerivative 2 0 v q ∧
      angularPartial (angularPartial v) q = mixedDerivative 0 2 v q := by
  have hvr : ContDiffOn ℝ ∞ (radialPartial v) Ω :=
    (hv.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hvt : ContDiffOn ℝ ∞ (angularPartial v) Ω :=
    (hv.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  exact ⟨(radialPartial_eq_mixedDerivative_on hΩ hvr hq).trans
    (mixedDerivative_radialPartial hΩ hv 1 0 hq),
    (angularPartial_eq_mixedDerivative_on hΩ hvt hq).trans
      (mixedDerivative_angularPartial hΩ hv 0 1 hq)⟩

/-- The negative potential is a polynomial in fixed geometric factors,
pulled height, and two coordinate derivatives of its reciprocal. -/
theorem n04PrincipalNegative_potential_partial_formula
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    {q : PolarPoint} (hq : q ∈ unitStrip) :
    let H : PolarPoint → ℝ := fun p =>
      K.height z m (K.inverseChart z m (canonicalUnitPoint K m p))
    let Q : PolarPoint → ℝ := fun p => (H p)⁻¹
    atom D T S C L K z m .potential q =
      -H q * ((K.right m - K.left m)⁻¹ ^ 2 * radialPartial (radialPartial Q) q -
        (canonicalUnitPoint K m q).1 * angularPartial (angularPartial Q) q) := by
  let H : PolarPoint → ℝ := fun p =>
    K.height z m (K.inverseChart z m (canonicalUnitPoint K m p))
  let Q : PolarPoint → ℝ := fun p => (H p)⁻¹
  have hunit : ContDiff ℝ ∞ (canonicalUnitPoint K m) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hQ : ContDiffOn ℝ ∞ Q unitStrip :=
    (n04PrincipalNegative_reciprocal_pulledHeight_smooth hA hz hs m).comp
      hunit.contDiffOn
      (fun p hp => n04PrincipalNegative_unitPoint_mem K m (hA.referenceBounds m).2.1 hp)
  have hpartials := n04PrincipalNegative_secondPartials
    (isOpen_Ioo.prod isOpen_univ) hQ hq
  change atom D T S C L K z m .potential q =
    -H q * ((K.right m - K.left m)⁻¹ ^ 2 * radialPartial (radialPartial Q) q -
      (canonicalUnitPoint K m q).1 * angularPartial (angularPartial Q) q)
  rw [hpartials.1, hpartials.2]
  exact n04PrincipalNegative_potential_unit_formula hA hB hz hs m hm hq

end ContinuousFlexibility.Analysis
