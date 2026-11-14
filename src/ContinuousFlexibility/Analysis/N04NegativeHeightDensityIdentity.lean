import ContinuousFlexibility.Analysis.ActualNegativePrincipalDensity
import ContinuousFlexibility.Analysis.RelativePrincipalCoefficients
import ContinuousFlexibility.Analysis.NegativeCanonicalEffectiveOperator

/-!
# Negative heights from the nonsingular angular density

The Airy principal density determines the physical height by the forward
chart and the radial physical coefficient.  Its angular numerator is
`φθ² - ξ ξθ²`; unlike the discriminant and the radial chart coordinate,
this expression does not vanish at a root.  The identity below therefore
introduces no division by a root coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

/-- The angular numerator in the adjugate pullback of the Airy field. -/
def n04NegativeHeightAngularFactor (F : PolarPoint → PolarPoint) (p : PolarPoint) : ℝ :=
  (fderiv ℝ F p (0, 1)).2 ^ 2 - (F p).1 * (fderiv ℝ F p (0, 1)).1 ^ 2

/-- The Airy density gives a forward-only identity for the actual height.
No inverse-coordinate or characteristic-coordinate estimate is assumed. -/
theorem n04NegativeHeight_angularFactor_eq_of_density
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (p : PolarPoint)
    (hJ : planeJacobian F p ≠ 0) (hh : h p ≠ 0)
    (ha : (coordinatePrincipalDensity A F h).a p = 1)
    (hb : (coordinatePrincipalDensity A F h).b p = 0)
    (hc : (coordinatePrincipalDensity A F h).c p = -(F p).1) :
    n04NegativeHeightAngularFactor F p = A.a p * h p ^ 2 * |planeJacobian F p| := by
  have hr := (adjugateCoordinatePrincipalCoefficients_eq_of_density
    A canonicalAiryPrincipalCoefficients F h p hJ hh ha.symm hb.symm hc.symm).1
  have hq : n04NegativeHeightAngularFactor F p / (h p ^ 2 * |planeJacobian F p|) =
      A.a p := by
    simpa only [n04NegativeHeightAngularFactor,
      adjugateCoordinatePrincipalCoefficients, canonicalAiryPrincipalCoefficients,
      coefficientQuadratic, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, neg_sq, neg_mul,
      ← sub_eq_add_neg, one_div, div_eq_mul_inv, mul_comm] using hr
  have he := (div_eq_iff
    (mul_ne_zero (pow_ne_zero 2 hh) (abs_ne_zero.mpr hJ))).mp hq
  simpa only [mul_assoc] using he

/-- Both square-root formulas use only strictly positive, regularized
factors.  The same expression supplies the height and its reciprocal. -/
theorem n04NegativeHeight_sqrt_eq_of_density
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (p : PolarPoint)
    (hJ : planeJacobian F p ≠ 0) (hh : 0 < h p) (hapos : 0 < A.a p)
    (ha : (coordinatePrincipalDensity A F h).a p = 1)
    (hb : (coordinatePrincipalDensity A F h).b p = 0)
    (hc : (coordinatePrincipalDensity A F h).c p = -(F p).1) :
    0 < n04NegativeHeightAngularFactor F p ∧
      h p = Real.sqrt (n04NegativeHeightAngularFactor F p /
        (A.a p * |planeJacobian F p|)) ∧
      (h p)⁻¹ = Real.sqrt ((A.a p * |planeJacobian F p|) /
        n04NegativeHeightAngularFactor F p) := by
  have he := n04NegativeHeight_angularFactor_eq_of_density A F h p hJ hh.ne' ha hb hc
  have hfactor : 0 < n04NegativeHeightAngularFactor F p := by
    rw [he]
    exact mul_pos (mul_pos hapos (sq_pos_of_pos hh)) (abs_pos.mpr hJ)
  have hsquare : h p ^ 2 = n04NegativeHeightAngularFactor F p /
      (A.a p * |planeJacobian F p|) := by
    apply (eq_div_iff (mul_ne_zero hapos.ne' (abs_ne_zero.mpr hJ))).mpr
    rw [he]
    ring
  have hisquare : (h p)⁻¹ ^ 2 = (A.a p * |planeJacobian F p|) /
      n04NegativeHeightAngularFactor F p := by
    rw [inv_pow, hsquare, inv_div]
  exact ⟨hfactor, by rw [← hsquare, Real.sqrt_sq hh.le],
    by rw [← hisquare, Real.sqrt_sq (inv_pos.mpr hh).le]⟩

/-- The literal chosen negative chart satisfies the nonsingular height
formula on its whole original component, including points past its
moving artificial cut. -/
theorem n04NegativeHeight_actualAtlas_sqrt_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    0 < n04NegativeHeightAngularFactor (K.chart z k) p ∧
      K.height z k p = Real.sqrt (n04NegativeHeightAngularFactor (K.chart z k) p /
        ((L.coefficients z).a p * |planeJacobian (K.chart z k) p|)) ∧
      (K.height z k p)⁻¹ = Real.sqrt (((L.coefficients z).a p *
        |planeJacobian (K.chart z k) p|) / n04NegativeHeightAngularFactor (K.chart z k) p) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hg := n04bActualTypedAtlas_negative_component_germs hT hS hN hfield e
    hz hs k m side hi hp
  have hregular := n04b_actualRootPhysical_regular_at hN hS hT hfield hz hs m side hp
  have hJ : planeJacobian (K.chart z k) p ≠ 0 := by
    unfold planeJacobian
    rw [hg.1.fderiv_eq]
    exact hregular.2.2.1
  have hh : 0 < K.height z k p := by
    rw [hg.2.self_of_nhds]
    exact hregular.2.2.2
  have hcontrol : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hp.1.1, hp.1.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hprincipal := n04Coordinates_actualAtlas_negativePrincipalDensity
    hT hS hN hfield e hz hs k m side hi hp
  exact n04NegativeHeight_sqrt_eq_of_density (L.coefficients z) (K.chart z k)
    (K.height z k) p hJ hh (hfield.positive_a z hz hs p hpD)
    hprincipal.1 hprincipal.2.1 hprincipal.2.2

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeHeight_actualAtlas_sqrt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeHeight_actualAtlas_sqrt_eq
