import ContinuousFlexibility.Analysis.StateProfileRegularity
import ContinuousFlexibility.Scalar.WeightedCompactRadial
import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Separating the actual border parameter from the optical controls

The nonzero supports of the border function and the optical controls lie
in opposite sign regions of the reference derivative.  This identifies
the actual profile germ on the border support without an assumed weighted
realization of the control sum.

The current true-border certificate contains the actual compact support
inside the core. It supplies a height realization for the distinguished
profile variation at every requested weight.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

theorem n07a_control_eq_zero_of_deriv_nonneg
    (hC : controlGeometryConditions D S C) (m : ℕ) {r : ℝ}
    (hr : 0 ≤ deriv D.w r) : C.control m r = 0 := by
  have hnegative := hC.2.2.2.1
  by_contra hne
  exact (not_lt_of_ge hr) (hnegative m r (hC.support_subset m hne))

theorem n07a_controlSum_eq_zero_of_deriv_nonneg
    (hC : controlGeometryConditions D S C) (x : AnnularState S) {r : ℝ}
    (hr : 0 ≤ deriv D.w r) : stateControlSum C x r = 0 := by
  simp only [stateControlSum, n07a_control_eq_zero_of_deriv_nonneg hC _ hr,
    mul_zero, tsum_zero]

theorem n07a_stateProfile_eq_nuProfile_of_deriv_nonneg
    (hC : controlGeometryConditions D S C) (x : AnnularState S) {r : ℝ}
    (hr : 0 ≤ deriv D.w r) :
    stateProfile D S C x r = D.w r * Real.exp (x.2.1 * D.chi r) := by
  change D.w r * Real.exp (x.2.1 * D.chi r + stateControlSum C x r) = _
  rw [n07a_controlSum_eq_zero_of_deriv_nonneg hC x hr, add_zero]

theorem n07a_stateProfile_eq_nuProfile_germ
    (hw : ContDiff ℝ ∞ D.w) (hC : controlGeometryConditions D S C)
    (x : AnnularState S) {r : ℝ} (hr : 0 < deriv D.w r) :
    stateProfile D S C x =ᶠ[𝓝 r]
      (fun t => D.w t * Real.exp (x.2.1 * D.chi t)) := by
  have hderiv : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  filter_upwards [hderiv.continuousAt.eventually (Ioi_mem_nhds hr)] with t ht
  exact n07a_stateProfile_eq_nuProfile_of_deriv_nonneg hC x ht.le

/-- The relative profile increment for the actual distinguished scalar. -/
def n07aNuProfileMean (D : ReferenceData) (ν r : ℝ) : ℝ :=
  Real.exp (ν * D.chi r) - 1

theorem n07aNuProfileMean_contDiff (hborder : RadialTrueBorder D) (ν : ℝ) :
    ContDiff ℝ ∞ (n07aNuProfileMean D ν) :=
  ((contDiff_const.mul hborder.1).exp).sub contDiff_const

theorem n07aNuProfileMean_compactRadialSupport
    (hborder : RadialTrueBorder D) (ν : ℝ) :
    HasCompactRadialSupport D (fun p => n07aNuProfileMean D ν p.1) := by
  refine ⟨tsupport D.chi, hborder.2.1, fun r hr => (hborder.2.2.1 hr).1, ?_⟩
  intro r hr θ
  have hχ : D.chi r = 0 := by
    by_contra hne
    exact hr (subset_tsupport D.chi hne)
  simp only [n07aNuProfileMean, hχ, mul_zero, Real.exp_zero, sub_self]

theorem n07aNuProfileMean_heightMember
    {T : MaterialData} (hT : IsMaterialData D T) (hborder : RadialTrueBorder D)
    (γ ν : ℝ) : HeightMember D T γ (fun p => n07aNuProfileMean D ν p.1) :=
  heightMember_radial_of_compact_support hT (n07aNuProfileMean_contDiff hborder ν)
    (n07aNuProfileMean_compactRadialSupport hborder ν)

/-- The distinguished profile increment in the actual model at any
weight, including the common height weight 3/4. -/
def n07aNuProfileHeight
    {T : MaterialData} (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D) (γ ν : ℝ) : (S.height γ).Space :=
  SobolevModelData.liftHeight (hS.1 γ) (fun p => n07aNuProfileMean D ν p.1)
    (n07aNuProfileMean_heightMember hT hborder γ ν)

theorem n07aNuProfileHeight_decode
    {T : MaterialData} (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hborder : RadialTrueBorder D) (γ ν : ℝ) :
    (S.height γ).decode (n07aNuProfileHeight hT hS hborder γ ν) =
      (fun p => n07aNuProfileMean D ν p.1) :=
  SobolevModelData.decode_liftHeight (hS.1 γ) _ _

end ContinuousFlexibility.Analysis
