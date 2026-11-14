module

public import ContinuousFlexibility.Analysis.N06PositiveCurrentTestLp
public import ContinuousFlexibility.Analysis.CanonicalPrincipalCoefficients
public import ContinuousFlexibility.Analysis.N06RootBoundaryCancellation

/-!
# The actual normal density at a turning root

N03 supplies a genuine germ of the original physical coefficients wherever
the reference slope is nonnegative, including each turning root. Thus the
actual physical coefficients are smooth near that root, even on the nearby
negative side. The existing negative normal-form theorem applies there.
Continuity of the true forward coordinate density then gives its closed
normal row `(1,0)`, without assuming smoothness on the whole negative piece.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Only continuous coefficient values and smooth forward first jets
are needed for continuity of the transported normal coefficient row. -/
theorem n06_coordinatePrincipalDensity_normal_continuousAt
    {A : SymmetricCoefficients} {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {x : PolarPoint} (ha : ContinuousAt A.a x) (hb : ContinuousAt A.b x)
    (hc : ContinuousAt A.c x) (hF : ContDiffAt ℝ ∞ F x) (hh : ContinuousAt h x)
    (hJ : planeJacobian F x ≠ 0) :
    ContinuousAt (coordinatePrincipalDensity A F h).a x ∧
      ContinuousAt (coordinatePrincipalDensity A F h).b x := by
  have hDF : ContDiffAt ℝ ∞ (fderiv ℝ F) x := hF.fderiv_right (by simp)
  have hfr : ContinuousAt (fun q => fderiv ℝ F q (1, 0)) x :=
    (hDF.clm_apply contDiffAt_const).continuousAt
  have hft : ContinuousAt (fun q => fderiv ℝ F q (0, 1)) x :=
    (hDF.clm_apply contDiffAt_const).continuousAt
  have hdet : ContinuousAt (planeJacobian F) x :=
    (hfr.fst.mul hft.snd).sub (hfr.snd.mul hft.fst)
  have hscale : ContinuousAt (fun q => h q ^ 2 / |planeJacobian F q|) x :=
    (hh.pow 2).div hdet.abs (abs_ne_zero.mpr hJ)
  constructor
  · exact hscale.mul
      (((ha.mul (hfr.fst.pow 2)).add
        (((continuousAt_const.mul hb).mul hfr.fst).mul hft.fst)).add
        (hc.mul (hft.fst.pow 2)))
  · exact hscale.mul
      ((((ha.mul hfr.fst).mul hfr.snd).add
        (hb.mul ((hfr.fst.mul hft.snd).add (hft.fst.mul hfr.snd)))).add
        ((hc.mul hft.fst).mul hft.snd))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The actual transported normal row equals `(1,0)` at any closed point
of a negative piece with nonnegative reference slope. In particular this
includes both possible turning endpoints, through the same statement. -/
theorem n06_negative_closed_normalDensity_of_nonneg
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = false) {x : PolarPoint}
    (hx : x ∈ physicalPieceClosed S K z m)
    (hp : x ∈ annularOpen D) (hpos : 0 ≤ deriv D.w x.1) :
    (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a x = 1 ∧
      (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b x = 0 := by
  have hreg := n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03 hz hs hp hpos
  have hcharts := (h04.1.boundary z hz hs m).2.2.2.2.1 x hx
  have hcont := n06_coordinatePrincipalDensity_normal_continuousAt
    hreg.1.continuousAt hreg.2.1.continuousAt hreg.2.2.continuousAt
    hcharts.1 hcharts.2.1.continuousAt hcharts.2.2.1
  have hnear : ∀ᶠ q in 𝓝 x,
      DifferentiableAt ℝ (L.coefficients z).a q ∧
        DifferentiableAt ℝ (L.coefficients z).b q ∧
        DifferentiableAt ℝ (L.coefficients z).c q := by
    filter_upwards [((hreg.1.of_le (m := 1) (by simp)).eventually (by simp)),
      ((hreg.2.1.of_le (m := 1) (by simp)).eventually (by simp)),
      ((hreg.2.2.of_le (m := 1) (by simp)).eventually (by simp))] with q hqa hqb hqc
    exact ⟨hqa.differentiableAt (by norm_num), hqb.differentiableAt (by norm_num),
      hqc.differentiableAt (by norm_num)⟩
  haveI : NeBot (𝓝[physicalPieceOpen S K z m] x) :=
    mem_closure_iff_nhdsWithin_neBot.mp hx
  have hrow : ∀ᶠ q in 𝓝[physicalPieceOpen S K z m] x,
      (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a q = 1 ∧
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b q = 0 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hmem
    have hn := negativePrincipalDensity_eq_normalForm
      (n06_N04_qualitative_parts h04).1 (n06_N04_qualitative_parts h04).2
      hz hs m hm hmem hq.1 hq.2.1 hq.2.2
    exact ⟨hn.1, hn.2.1⟩
  exact ⟨tendsto_nhds_unique_of_eventuallyEq
      (hcont.1.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
      (hrow.mono (fun _ hq => hq.1)),
    tendsto_nhds_unique_of_eventuallyEq
      (hcont.2.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
      (hrow.mono (fun _ hq => hq.2))⟩

/-- Specializing the actual slope to zero gives the turning-root row;
neither endpoint is distinguished by this formulation. -/
theorem n06_negative_turningRoot_normalDensity
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = false) {x : PolarPoint}
    (hx : x ∈ physicalPieceClosed S K z m)
    (hp : x ∈ annularOpen D) (hroot : deriv D.w x.1 = 0) :
    (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a x = 1 ∧
      (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b x = 0 :=
  n06_negative_closed_normalDensity_of_nonneg hT hS h01 h03 h04 hz hs m hm hx hp
    (le_of_eq hroot.symm)

end ContinuousFlexibility.Statements
