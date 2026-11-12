import ContinuousFlexibility.Analysis.N07aLocalPullbackEquation
import ContinuousFlexibility.Analysis.N07aClosedChartDifferentials

/-!
# The actual negative normal symbol, including the moving cut

A radial quadratic probe in N04 identifies the normal symbol of the
ungauged pullback. Its value and first derivatives vanish at the testing
point, so the height contributes exactly its square. The identity then
extends to the canonical closure using the stored boundary inverse germs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open N07aClosedJets
open scoped Topology ContDiff

/-- At a zero first jet, multiplication introduces no cross terms in the
divergence operator. -/
theorem n07a_divergence_mul_at_zero_firstJet
    {U : Set PolarPoint} (hU : IsOpen U) {L : SymmetricCoefficients}
    {h g : PolarPoint → ℝ} (ha : ContDiffOn ℝ ∞ L.a U)
    (hb : ContDiffOn ℝ ∞ L.b U) (hc : ContDiffOn ℝ ∞ L.c U)
    (hh : ContDiffOn ℝ ∞ h U) (hg : ContDiffOn ℝ ∞ g U)
    {x : PolarPoint} (hx : x ∈ U)
    (hg0 : g x = 0) (hgr : radialPartial g x = 0)
    (hgt : angularPartial g x = 0) :
    divergenceOperator L (fun q => h q * g q) x =
      h x * divergenceOperator L g x := by
  let Nh := fun q => L.a q * radialPartial h q + L.b q * angularPartial h q
  let Ng := fun q => L.a q * radialPartial g q + L.b q * angularPartial g q
  let Ah := fun q => L.b q * radialPartial h q + L.c q * angularPartial h q
  let Ag := fun q => L.b q * radialPartial g q + L.c q * angularPartial g q
  have hhr := n07a_localPullback_radial_smooth hU hh
  have hht := n07a_localPullback_angular_smooth hU hh
  have hgrs := n07a_localPullback_radial_smooth hU hg
  have hgts := n07a_localPullback_angular_smooth hU hg
  have hNh : ContDiffOn ℝ ∞ Nh U := (ha.mul hhr).add (hb.mul hht)
  have hNg : ContDiffOn ℝ ∞ Ng U := (ha.mul hgrs).add (hb.mul hgts)
  have hAh : ContDiffOn ℝ ∞ Ah U := (hb.mul hhr).add (hc.mul hht)
  have hAg : ContDiffOn ℝ ∞ Ag U := (hb.mul hgrs).add (hc.mul hgts)
  have hdh := (hh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdg := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdNh := (hNh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdNg := (hNg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdAh := (hAh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdAg := (hAg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hnormal :
      (fun q => L.a q * radialPartial (fun p => h p * g p) q +
        L.b q * angularPartial (fun p => h p * g p) q)
        =ᶠ[𝓝 x] (fun q => h q * Ng q + g q * Nh q) := by
    filter_upwards [hU.mem_nhds hx] with q hq
    have hdqh := (hh.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
    have hdqg := (hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
    rw [radialPartial_mul hdqh hdqg, angularPartial_mul hdqh hdqg]
    dsimp only [Ng, Nh]
    ring
  have hangular :
      (fun q => L.b q * radialPartial (fun p => h p * g p) q +
        L.c q * angularPartial (fun p => h p * g p) q)
        =ᶠ[𝓝 x] (fun q => h q * Ag q + g q * Ah q) := by
    filter_upwards [hU.mem_nhds hx] with q hq
    have hdqh := (hh.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
    have hdqg := (hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
    rw [radialPartial_mul hdqh hdqg, angularPartial_mul hdqh hdqg]
    dsimp only [Ag, Ah]
    ring
  have hnormal' := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) hnormal.fderiv_eq
  have hangular' := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) hangular.fderiv_eq
  have hNg0 : Ng x = 0 := by simp only [Ng, hgr, hgt, mul_zero, add_zero]
  have hAg0 : Ag x = 0 := by simp only [Ag, hgr, hgt, mul_zero, add_zero]
  change radialPartial _ x + angularPartial _ x = _
  rw [show radialPartial _ x = radialPartial (fun q => h q * Ng q + g q * Nh q) x
      from hnormal',
    show angularPartial _ x = angularPartial (fun q => h q * Ag q + g q * Ah q) x
      from hangular',
    radialPartial_add (hdh.mul hdNg) (hdg.mul hdNh),
    angularPartial_add (hdh.mul hdAg) (hdg.mul hdAh),
    radialPartial_mul hdh hdNg, radialPartial_mul hdg hdNh,
    angularPartial_mul hdh hdAg, angularPartial_mul hdg hdAh,
    hg0, hgr, hgt, hNg0, hAg0]
  simp only [zero_mul, mul_zero, zero_add, add_zero]
  change h x * radialPartial Ng x + h x * angularPartial Ag x =
    h x * (radialPartial Ng x + angularPartial Ag x)
  ring

/-- The globally smooth probe has one unit radial second derivative. -/
def n07aRadialQuadraticProbe (y : PolarPoint) (q : PolarPoint) : ℝ :=
  (1 / 2 : ℝ) * (q.1 - y.1) ^ 2

theorem n07a_radialQuadraticProbe_smooth (y : PolarPoint) :
    ContDiff ℝ ∞ (n07aRadialQuadraticProbe y) :=
  contDiff_const.mul ((contDiff_fst.sub contDiff_const).pow 2)

theorem n07a_radialQuadraticProbe_radial (y : PolarPoint) :
    radialPartial (n07aRadialQuadraticProbe y) = fun q => q.1 - y.1 := by
  funext q
  unfold n07aRadialQuadraticProbe
  rw [radialPartial_mul differentiableAt_const
      ((differentiableAt_fst.sub differentiableAt_const).pow 2),
    radialPartial_const, radialPartial_sq (differentiableAt_fst.sub differentiableAt_const),
    radialPartial_sub differentiableAt_fst differentiableAt_const,
    radialPartial_fst, radialPartial_const]
  ring

theorem n07a_radialQuadraticProbe_angular (y : PolarPoint) :
    angularPartial (n07aRadialQuadraticProbe y) = fun _ => 0 := by
  funext q
  unfold n07aRadialQuadraticProbe
  rw [angularPartial_mul differentiableAt_const
      ((differentiableAt_fst.sub differentiableAt_const).pow 2),
    angularPartial_const, angularPartial_sq (differentiableAt_fst.sub differentiableAt_const),
    angularPartial_sub differentiableAt_fst differentiableAt_const,
    angularPartial_fst, angularPartial_const]
  ring

theorem n07a_radialQuadraticProbe_mixed (y : PolarPoint) :
    mixedDerivative 2 0 (n07aRadialQuadraticProbe y) y = 1 ∧
      mixedDerivative 1 1 (n07aRadialQuadraticProbe y) y = 0 ∧
      mixedDerivative 0 2 (n07aRadialQuadraticProbe y) y = 0 ∧
      mixedDerivative 1 0 (n07aRadialQuadraticProbe y) y = 0 ∧
      mixedDerivative 0 1 (n07aRadialQuadraticProbe y) y = 0 := by
  have hW : ContDiffOn ℝ ∞ (n07aRadialQuadraticProbe y) (univ : Set PolarPoint) :=
    (n07a_radialQuadraticProbe_smooth y).contDiffOn
  have hr := n07a_localPullback_radial_smooth isOpen_univ hW
  have ht := n07a_localPullback_angular_smooth isOpen_univ hW
  have hrr := (radialPartial_eq_mixedDerivative_on isOpen_univ hr (mem_univ y)).trans
    (mixedDerivative_radialPartial isOpen_univ hW 1 0 (mem_univ y))
  have hrt := (angularPartial_eq_mixedDerivative_on isOpen_univ hr (mem_univ y)).trans
    (mixedDerivative_radialPartial isOpen_univ hW 0 1 (mem_univ y))
  have htt := (angularPartial_eq_mixedDerivative_on isOpen_univ ht (mem_univ y)).trans
    (mixedDerivative_angularPartial isOpen_univ hW 0 1 (mem_univ y))
  have hr0 := radialPartial_eq_mixedDerivative_on isOpen_univ hW (mem_univ y)
  have ht0 := angularPartial_eq_mixedDerivative_on isOpen_univ hW (mem_univ y)
  rw [← hrr, ← hrt, ← htt, ← hr0, ← ht0,
    n07a_radialQuadraticProbe_radial, n07a_radialQuadraticProbe_angular]
  simp [radialPartial_sub differentiableAt_fst differentiableAt_const,
    angularPartial_sub differentiableAt_fst differentiableAt_const]

/-- The normal symbol depends only on the first derivative of the chart. -/
theorem n07a_localPullback_principal_fderiv_congr
    {L : SymmetricCoefficients} {F F' : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hF' : DifferentiableAt ℝ F' x)
    (he : fderiv ℝ F x = fderiv ℝ F' x) :
    (n07aPullbackPrincipal L F).a x = (n07aPullbackPrincipal L F').a x := by
  have hr : fderiv ℝ (fun q => (F q).1) x =
      fderiv ℝ (fun q => (F' q).1) x := by
    rw [fderiv.fst hF, fderiv.fst hF', he]
  simp only [n07aPullbackPrincipal, radialPartial, angularPartial, hr]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- N04 determines the actual ungauged normal symbol on every negative piece. -/
theorem n07a_actual_negativePullback_principal_identity
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D))
    (m : ℕ) (hm : K.positive m = false)
    {y : PolarPoint} (hy : y ∈ canonicalOpen S K m) :
    K.height z m (K.inverseChart z m y) ^ 2 *
        (n07aPullbackPrincipal (L.coefficients z) (K.chart z m)).a
          (K.inverseChart z m y) =
      |planeJacobian (K.chart z m) (K.inverseChart z m y)| := by
  let x := K.inverseChart z m y
  let W := n07aRadialQuadraticProbe y
  let g := W ∘ K.chart z m
  have hdom := h04.1.domains z hz hs m
  have hchart := h04.1.charts z hz hs m
  have hx : x ∈ physicalPieceOpen S K z m := hchart.2.1 hy
  have hxy : K.chart z m x = y := hchart.2.2.2.1 y hy
  have hF := hchart.2.2.2.2.1
  have hh := hchart.2.2.2.2.2.2.1
  have hW : ContDiff ℝ ∞ W := n07a_radialQuadraticProbe_smooth y
  have hg : ContDiffOn ℝ ∞ g (physicalPieceOpen S K z m) :=
    hW.contDiffOn.comp hF (mapsTo_univ _ _)
  have hdF := (hF.contDiffAt (hdom.1.mem_nhds hx)).differentiableAt (by simp)
  have hdW := hW.differentiable (by simp) (K.chart z m x)
  have hW0 : W y = 0 := by simp [W, n07aRadialQuadraticProbe]
  have hWr0 : radialPartial W y = 0 := by
    simp only [W, n07a_radialQuadraticProbe_radial, sub_self]
  have hWt0 : angularPartial W y = 0 := by
    simp only [W, n07a_radialQuadraticProbe_angular]
  have hg0 : g x = 0 := by simpa only [g, Function.comp_apply, hxy] using hW0
  have hgr0 : radialPartial g x = 0 := by
    rw [n07a_localPullback_radial_chain hdF hdW, hxy, hWr0, hWt0]
    ring
  have hgt0 : angularPartial g x = 0 := by
    rw [n07a_localPullback_angular_chain hdF hdW, hxy, hWr0, hWt0]
    ring
  have hmul := n07a_divergence_mul_at_zero_firstJet hdom.1
    (ha.mono hdom.2.2.1) (hb.mono hdom.2.2.1) (hc.mono hdom.2.2.1)
    hh hg hx hg0 hgr0 hgt0
  have hchain := n07a_localPullback_divergence_chain hdom.1 isOpen_univ
    (ha.mono hdom.2.2.1) (hb.mono hdom.2.2.1) (hc.mono hdom.2.2.1)
    hF hW.contDiffOn (mapsTo_univ _ _) hx
  have hj := n07a_radialQuadraticProbe_mixed y
  rw [hxy] at hchain
  have hphysical : divergenceOperator (L.coefficients z) g x =
      (n07aPullbackPrincipal (L.coefficients z) (K.chart z m)).a x := by
    simpa only [W, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2,
      mul_one, mul_zero, add_zero] using hchain
  have hnear : ∀ᶠ q in 𝓝 y, q ∈ canonicalOpen S K m :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hy
  have hnormal :
      (fun q => (K.coefficients z m).a q * radialPartial W q +
        (K.coefficients z m).b q * angularPartial W q)
        =ᶠ[𝓝 y] radialPartial W := by
    filter_upwards [hnear] with q hq
    have hqneg := h04.2.1.2.2.2.1 z hz hs m hm q hq
    simp only [hqneg.1, hqneg.2.1, one_mul, zero_mul, add_zero]
  have hangular :
      (fun q => (K.coefficients z m).b q * radialPartial W q +
        (K.coefficients z m).c q * angularPartial W q)
        =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [hnear] with q hq
    have hqneg := h04.2.1.2.2.2.1 z hz hs m hm q hq
    simp only [hqneg.2.1, W, n07a_radialQuadraticProbe_angular,
      zero_mul, mul_zero, add_zero]
  have hcanonical : divergenceOperator (K.coefficients z m) W y = 1 := by
    have he := congrArg₂ (fun r t : PolarPoint →L[ℝ] ℝ => r (1, 0) + t (0, 1))
      hnormal.fderiv_eq hangular.fderiv_eq
    change divergenceOperator (K.coefficients z m) W y =
      radialPartial (radialPartial W) y + angularPartial (fun _ => 0) y at he
    simpa [W, n07a_radialQuadraticProbe_radial,
      radialPartial_sub differentiableAt_fst differentiableAt_const] using he
  have hop := h04.2.1.2.2.1 z hz hs m W hW y hy
  simp only [canonicalOperator, canonicalSource, hm, Bool.false_eq_true,
    ↓reduceIte, one_mul, hcanonical, hW0, mul_zero, add_zero] at hop
  change K.height z m x * divergenceOperator (L.coefficients z)
    (fun q => K.height z m q * g q) x / |planeJacobian (K.chart z m) x| = 1 at hop
  rw [hmul, hphysical] at hop
  have heq := (div_eq_iff (abs_ne_zero.mpr (hchart.2.2.2.2.2.2.2 x hx).2.1)).mp hop
  calc
    _ = K.height z m x * (K.height z m x *
        (n07aPullbackPrincipal (L.coefficients z) (K.chart z m)).a x) := by ring
    _ = _ := by simpa only [one_mul] using heq

/-- The quadratic-probe identity persists at the actual closed endpoints. -/
theorem n07a_actual_negativePullback_principal_identity_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D))
    (m : ℕ) (hm : K.positive m = false)
    {y : PolarPoint} (hy : y ∈ canonicalClosed S K m)
    (hyD : K.inverseChart z m y ∈ annularOpen D) :
    K.height z m (K.inverseChart z m y) ^ 2 *
        (n07aPullbackPrincipal (L.coefficients z) (K.chart z m)).a
          (K.inverseChart z m y) =
      |planeJacobian (K.chart z m) (K.inverseChart z m y)| := by
  have hG := n04b_inverseChart_contDiffAt_closed h04.1 hz hs m hy
  have hboundary := h04.1.boundary z hz hs m
  have hp := hboundary.2.2.2.2.1 _ (hboundary.2.1 hy)
  have hD : annularOpen D ∈ 𝓝 (K.inverseChart z m y) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hyD
  have hα := (n07a_localPullback_principal_contDiffAt
    (ha.contDiffAt hD) (hb.contDiffAt hD) (hc.contDiffAt hD) hp.1).1
  have hcl : y ∈ closure (canonicalOpen S K m) := by
    rw [show canonicalOpen S K m = openStrip (K.left m) (K.right m) from rfl,
      closure_openStrip (h04.1.referenceBounds m).2.1]
    exact hy
  apply n07a_eq_of_continuousAt_of_eqOn_closure hcl
    (((hp.2.1.continuousAt.comp hG.continuousAt).pow 2).mul
      (hα.continuousAt.comp hG.continuousAt))
    (((contDiffAt_planeJacobian hp.1).continuousAt.comp hG.continuousAt).abs)
  intro q hq
  exact n07a_actual_negativePullback_principal_identity h04 hz hs ha hb hc m hm hq

/-- The actual negative normal coefficient is nonzero at a moving cut.
Only the geometry and the physical coefficient regularity enter. -/
theorem n07a_actual_negativePullback_principal_ne_zero_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D))
    (m : ℕ) (hm : K.positive m = false)
    {y : PolarPoint} (hy : y ∈ canonicalClosed S K m)
    (hyD : K.inverseChart z m y ∈ annularOpen D) :
    (n07aPullbackPrincipal (L.coefficients z) (K.chart z m)).a
      (K.inverseChart z m y) ≠ 0 := by
  have heq := n07a_actual_negativePullback_principal_identity_closed
    h04 hz hs ha hb hc m hm hy hyD
  have hbnd := h04.1.boundary z hz hs m
  have hJ := (hbnd.2.2.2.2.1 _ (hbnd.2.1 hy)).2.2.1
  intro hzero
  rw [hzero, mul_zero] at heq
  exact (abs_ne_zero.mpr hJ) heq.symm

/-- A smooth tubular chart with the same first jet inherits the actual
noncharacteristic normal direction. -/
theorem n07a_actual_negativePullback_principal_ne_zero_of_fderiv_eq_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D))
    (m : ℕ) (hm : K.positive m = false)
    {y : PolarPoint} (hy : y ∈ canonicalClosed S K m)
    (hyD : K.inverseChart z m y ∈ annularOpen D)
    {F : PolarPoint → PolarPoint}
    (hF : DifferentiableAt ℝ F (K.inverseChart z m y))
    (he : fderiv ℝ F (K.inverseChart z m y) =
      fderiv ℝ (K.chart z m) (K.inverseChart z m y)) :
    (n07aPullbackPrincipal (L.coefficients z) F).a (K.inverseChart z m y) ≠ 0 := by
  have hbnd := h04.1.boundary z hz hs m
  have hchart := (hbnd.2.2.2.2.1 _ (hbnd.2.1 hy)).1.differentiableAt (by simp)
  rw [n07a_localPullback_principal_fderiv_congr hF hchart he]
  exact n07a_actual_negativePullback_principal_ne_zero_closed
    h04 hz hs ha hb hc m hm hy hyD

end ContinuousFlexibility.Analysis
