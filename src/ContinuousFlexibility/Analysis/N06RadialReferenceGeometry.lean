import ContinuousFlexibility.Analysis.N06ReferencePhysicalCoefficients
import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities

/-!
# Explicit radial reference geometry in the actual canonical operator

For the actual reference chart (Y(r), theta) and height H(r), the principal
density and constant-test identities determine all scalar coefficients.
Only germs of the chart and height are used, so these formulas also apply
to a construction that changes its extensions away from a physical piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

def n06RadialReferenceA (w H Y R : ℝ → ℝ) (y : ℝ) : ℝ :=
  H (R y) ^ 2 * w (R y) * deriv Y (R y)

def n06RadialReferenceC (w H Y R : ℝ → ℝ) (y : ℝ) : ℝ :=
  H (R y) ^ 2 * (deriv w (R y) / R y) / deriv Y (R y)

def n06RadialReferenceQ (w Y R : ℝ → ℝ) (y : ℝ) : ℝ :=
  (deriv w (R y) / R y) / (w (R y) * deriv Y (R y) ^ 2)

def n06RadialReferenceV (w H Y R : ℝ → ℝ) (y : ℝ) : ℝ :=
  -(H (R y) * (deriv w (R y) * deriv H (R y) +
    w (R y) * deriv (deriv H) (R y))) / deriv Y (R y)

/-- The two columns and determinant of the actual chart derivative are
computed from its radial germ. -/
theorem n06_radialChart_derivative_of_germ
    {F : PolarPoint → PolarPoint} {Y : ℝ → ℝ} {p : PolarPoint}
    (hF : F =ᶠ[𝓝 p] fun q : PolarPoint => (Y q.1, q.2))
    (hY : DifferentiableAt ℝ Y p.1) :
    fderiv ℝ F p (1, 0) = (deriv Y p.1, 0) ∧
      fderiv ℝ F p (0, 1) = (0, 1) ∧
      planeJacobian F p = deriv Y p.1 := by
  have hd : HasFDerivAt (fun q : PolarPoint => (Y q.1, q.2))
      ((deriv Y p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    exact (hY.hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have he := (hF.fderiv_eq (𝕜 := ℝ)).trans hd.fderiv
  have hr : fderiv ℝ F p (1, 0) = (deriv Y p.1, 0) := by
    simp only [he, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one]
  have ht : fderiv ℝ F p (0, 1) = (0, 1) := by
    simp only [he, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero]
  exact ⟨hr, ht, by simp only [planeJacobian, hr, ht, mul_one, mul_zero, sub_zero]⟩

theorem n06_coordinatePrincipalDensity_radial
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {w H Y : ℝ → ℝ} {p : PolarPoint}
    (hF : F =ᶠ[𝓝 p] fun q : PolarPoint => (Y q.1, q.2))
    (hH : h p = H p.1) (hY : DifferentiableAt ℝ Y p.1)
    (hYpos : 0 < deriv Y p.1)
    (ha : A.a p = w p.1) (hb : A.b p = 0)
    (hc : A.c p = deriv w p.1 / p.1) :
    (coordinatePrincipalDensity A F h).a p = H p.1 ^ 2 * w p.1 * deriv Y p.1 ∧
      (coordinatePrincipalDensity A F h).b p = 0 ∧
      (coordinatePrincipalDensity A F h).c p =
        H p.1 ^ 2 * (deriv w p.1 / p.1) / deriv Y p.1 := by
  obtain ⟨hr, ht, hJ⟩ := n06_radialChart_derivative_of_germ hF hY
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [coordinatePrincipalDensity, coefficientQuadratic, hr, ht, hJ,
      abs_of_pos hYpos, hH, ha, hb, hc, zero_pow two_ne_zero, one_pow,
      mul_zero, zero_mul, add_zero, zero_add, mul_one]
  · field_simp [hYpos.ne']
    <;> ring
  · ring

/-- A radial height germ has the radial divergence of w H'. No regularity
of the unused angular coefficient is required for this identity. -/
theorem n06_divergence_radialHeight_of_germs
    {A : SymmetricCoefficients} {h : PolarPoint → ℝ}
    {w H : ℝ → ℝ} {p : PolarPoint}
    (ha : A.a =ᶠ[𝓝 p] fun q => w q.1)
    (hb : A.b =ᶠ[𝓝 p] fun _ => 0)
    (hh : h =ᶠ[𝓝 p] Radial.radialHeightField H)
    (hw : DifferentiableAt ℝ w p.1) (hH : ContDiff ℝ ∞ H) :
    divergenceOperator A h p =
      deriv w p.1 * deriv H p.1 + w p.1 * deriv (deriv H) p.1 := by
  have hHr : radialPartial h =ᶠ[𝓝 p] fun q => deriv H q.1 := by
    filter_upwards [hh.fderiv (𝕜 := ℝ)] with q hq
    change fderiv ℝ h q (1, 0) = _
    rw [hq]
    exact Radial.radialPartial_radialHeightField (hH.differentiable (by simp) q.1)
  have hHt : angularPartial h =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hh.fderiv (𝕜 := ℝ)] with q hq
    change fderiv ℝ h q (0, 1) = _
    rw [hq]
    exact Radial.angularPartial_radialHeightField (hH.differentiable (by simp) q.1)
  have hfluxR : (fun q => A.a q * radialPartial h q + A.b q * angularPartial h q)
      =ᶠ[𝓝 p] Radial.radialHeightField (fun r => w r * deriv H r) := by
    filter_upwards [ha, hb, hHr, hHt] with q hqa hqb hqr hqt
    simp only [hqa, hqb, hqr, hqt, Radial.radialHeightField, mul_zero, add_zero]
  have hfluxT : (fun q => A.b q * radialPartial h q + A.c q * angularPartial h q)
      =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hb, hHt] with q hqb hqt
    simp only [hqb, hqt, zero_mul, mul_zero, zero_add]
  have hH' : DifferentiableAt ℝ (deriv H) p.1 :=
    (contDiff_infty_iff_deriv.mp hH).2.differentiable (by simp) p.1
  change fderiv ℝ _ p (1, 0) + fderiv ℝ _ p (0, 1) = _
  rw [hfluxR.fderiv_eq, hfluxT.fderiv_eq]
  change radialPartial (Radial.radialHeightField (fun r => w r * deriv H r)) p +
    angularPartial (fun _ : PolarPoint => (0 : ℝ)) p = _
  have hrad : radialPartial (Radial.radialHeightField (fun r => w r * deriv H r)) p =
      deriv (fun r => w r * deriv H r) p.1 :=
    Radial.radialPartial_radialHeightField (h := fun r => w r * deriv H r) (hw.mul hH')
  rw [hrad, angularPartial_const, add_zero, deriv_fun_mul hw hH']

/-- The actual canonical principal coefficients at the reference state
are radial once the constructed reference chart and height have these
radial germs. The coefficient regularity is qualitative, without a bound. -/
theorem n06_canonicalReference_coefficients_radial
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R0 : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hN03 : N03Properties D T S C R0 L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hw : ContDiff ℝ ∞ D.w) (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState)
    (m : ℕ) (hm : K.positive m = true)
    {Y H R : ℝ → ℝ} (hY : ContDiff ℝ ∞ Y)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m)
    (hi : K.inverseChart (C.referenceState, 0) m p = (R p.1, p.2))
    (hchart : K.chart (C.referenceState, 0) m
      =ᶠ[𝓝 (K.inverseChart (C.referenceState, 0) m p)]
        fun q : PolarPoint => (Y q.1, q.2))
    (hheight : K.height (C.referenceState, 0) m
      =ᶠ[𝓝 (K.inverseChart (C.referenceState, 0) m p)] Radial.radialHeightField H)
    (hYpos : 0 < deriv Y (R p.1)) (hr : R p.1 ≠ 0)
    (hKa : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).a p)
    (hKb : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).b p)
    (hKc : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).c p) :
    (K.coefficients (C.referenceState, 0) m).a p = n06RadialReferenceA D.w H Y R p.1 ∧
      (K.coefficients (C.referenceState, 0) m).b p = 0 ∧
      (K.coefficients (C.referenceState, 0) m).c p = n06RadialReferenceC D.w H Y R p.1 := by
  let x := K.inverseChart (C.referenceState, 0) m p
  have hx : x ∈ referencePhysicalPieceOpen S K m := by
    have hxActual := (hA.charts (C.referenceState, 0) hz hs m).2.1 hp
    simpa only [hA.referenceDomain m] using hxActual
  have hxi : x.1 = R p.1 := congrArg Prod.fst hi
  have hg := n06_correctedReference_positivePiece_germ hN03 hA hw href hz hs m hm hx
  have hwa : DifferentiableAt ℝ (fun q : PolarPoint => D.w q.1) x :=
    (hw.differentiable (by simp) x.1).comp x differentiableAt_fst
  have hrx : x.1 ≠ 0 := by rw [hxi]; exact hr
  have hsingle : DifferentiableAt ℝ (fun r : ℝ => deriv D.w r / r) x.1 :=
    ((contDiff_infty_iff_deriv.mp hw).2.differentiable (by simp) x.1).div
      differentiableAt_id hrx
  have hwc : DifferentiableAt ℝ (fun q : PolarPoint => deriv D.w q.1 / q.1) x :=
    hsingle.comp x differentiableAt_fst
  have hdensity := canonicalPrincipalCoefficients_eq_density hA hB hz hs m hp
    (hwa.congr_of_eventuallyEq hg.1)
    ((differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hg.2.1)
    (hwc.congr_of_eventuallyEq hg.2.2) hKa hKb hKc
  have hformula := n06_coordinatePrincipalDensity_radial hchart hheight.eq_of_nhds
    (hY.differentiable (by simp) x.1) (by simpa only [x, hi] using hYpos)
    hg.1.eq_of_nhds hg.2.1.eq_of_nhds hg.2.2.eq_of_nhds
  refine ⟨hdensity.1.trans ?_, hdensity.2.1.trans hformula.2.1, hdensity.2.2.trans ?_⟩
  · simpa only [x, hi, n06RadialReferenceA] using hformula.1
  · simpa only [x, hi, n06RadialReferenceC] using hformula.2.2

/-- The constant-test identity fixes the actual potential, with the
positive-piece sign. Its formula involves only w, H, and Y. -/
theorem n06_canonicalReference_potential_radial
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R0 : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hN03 : N03Properties D T S C R0 L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hw : ContDiff ℝ ∞ D.w) (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState)
    (m : ℕ) (hm : K.positive m = true)
    {Y H R : ℝ → ℝ} (hY : ContDiff ℝ ∞ Y) (hH : ContDiff ℝ ∞ H)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m)
    (hi : K.inverseChart (C.referenceState, 0) m p = (R p.1, p.2))
    (hchart : K.chart (C.referenceState, 0) m
      =ᶠ[𝓝 (K.inverseChart (C.referenceState, 0) m p)]
        fun q : PolarPoint => (Y q.1, q.2))
    (hheight : K.height (C.referenceState, 0) m
      =ᶠ[𝓝 (K.inverseChart (C.referenceState, 0) m p)] Radial.radialHeightField H)
    (hYpos : 0 < deriv Y (R p.1)) :
    K.potential (C.referenceState, 0) m p = n06RadialReferenceV D.w H Y R p.1 := by
  let x := K.inverseChart (C.referenceState, 0) m p
  have hx : x ∈ referencePhysicalPieceOpen S K m := by
    have hxActual := (hA.charts (C.referenceState, 0) hz hs m).2.1 hp
    simpa only [hA.referenceDomain m] using hxActual
  have hxi : x.1 = R p.1 := congrArg Prod.fst hi
  have hg := n06_correctedReference_positivePiece_germ hN03 hA hw href hz hs m hm hx
  have hdiv := n06_divergence_radialHeight_of_germs hg.1 hg.2.1 hheight
    (hw.differentiable (by simp) x.1) hH
  have hJac := (n06_radialChart_derivative_of_germ hchart
    (hY.differentiable (by simp) x.1)).2.2
  have hpotential := canonicalPotential_eq_source_height hB hz hs m hp
  have hYpos' : 0 < deriv Y x.1 := by simpa only [hxi] using hYpos
  change K.potential (C.referenceState, 0) m p =
    (if K.positive m then -1 else (1 : ℝ)) *
      (K.height (C.referenceState, 0) m x *
        divergenceOperator (L.coefficients (C.referenceState, 0))
          (K.height (C.referenceState, 0) m) x /
        |planeJacobian (K.chart (C.referenceState, 0) m) x|) at hpotential
  rw [hm, if_pos rfl, hheight.eq_of_nhds, hdiv, hJac, abs_of_pos hYpos'] at hpotential
  simpa only [Radial.radialHeightField, x, hi, n06RadialReferenceV,
    neg_mul, one_mul, neg_div] using hpotential

/-- The quotient c/a is fixed by the radial coordinate slope; the height
factor cancels. This is the exact q used by the weak modal estimate. -/
theorem n06_radialReferenceC_eq_aq
    (w H Y R : ℝ → ℝ) (y : ℝ)
    (hw : w (R y) ≠ 0) (hY : deriv Y (R y) ≠ 0) :
    n06RadialReferenceC w H Y R y =
      n06RadialReferenceA w H Y R y * n06RadialReferenceQ w Y R y := by
  dsimp only [n06RadialReferenceC, n06RadialReferenceA, n06RadialReferenceQ]
  field_simp [hw, hY]
  <;> ring

end ContinuousFlexibility.Analysis
