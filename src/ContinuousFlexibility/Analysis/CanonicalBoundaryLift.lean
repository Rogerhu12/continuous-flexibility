import ContinuousFlexibility.Analysis.CanonicalBoundaryImage
import ContinuousFlexibility.Analysis.ParameterizedCircleInverse
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Genuine angular lifts on actual closed canonical boundaries

Periodicity of the current physical domain lets the interior lift law
extend to its actual closure. On a true horizontal physical circle with
constant canonical radial image, the nonzero Jacobian forces a positive
angular derivative. The resulting boundary map is a genuine smooth
increasing circle lift. Moving cut curves are not treated as fixed
physical radial endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A nonvanishing actual derivative of a degree-one lift has positive
sign. Darboux's theorem rules out a change of sign, and the period rules
out the negative sign. -/
theorem deriv_pos_of_periodic_lift_of_ne_zero
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hperiod : ∀ θ, f (θ + T) = f θ + T)
    (hne : ∀ θ, deriv f θ ≠ 0) : ∀ θ, 0 < deriv f θ := by
  have hf : Differentiable ℝ f := fun θ => differentiableAt_of_deriv_ne_zero (hne θ)
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne
      (f := f) (f' := deriv f) (s := (univ : Set ℝ)) (m := 0) convex_univ
      (fun θ _ => (hf θ).hasDerivAt.hasDerivWithinAt) (fun θ _ => hne θ) with
    hneg | hpos
  · have hanti : StrictAnti f := strictAnti_of_deriv_neg (fun θ => hneg θ (mem_univ θ))
    have hlt : f T < f 0 := hanti hT
    have he : f T = f 0 + T := by simpa only [zero_add] using hperiod 0
    linarith
  · exact fun θ => hpos θ (mem_univ θ)

/-- A translation identity on a set extends to a closure point where the
two actual functions are continuous. -/
theorem periodic_lift_at_closure
    {U : Set PolarPoint} {F : PolarPoint → PolarPoint} {p v : PolarPoint}
    (hp : p ∈ closure U) (hF : ContinuousAt F p) (hFv : ContinuousAt F (p + v))
    (hperiod : ∀ q ∈ U, F (q + v) = F q + v) :
    F (p + v) = F p + v := by
  haveI : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hadd : ContinuousAt (fun q : PolarPoint => q + v) p :=
    continuousAt_id.add continuousAt_const
  have hl : ContinuousAt (fun q : PolarPoint => F (q + v)) p :=
    ContinuousAt.comp (f := fun q : PolarPoint => q + v) (x := p) hFv hadd
  have hr : ContinuousAt (fun q : PolarPoint => F q + v) p :=
    hF.add continuousAt_const
  have he : (fun q : PolarPoint => F (q + v)) =ᶠ[𝓝[U] p]
      (fun q : PolarPoint => F q + v) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hperiod q hq
  exact tendsto_nhds_unique_of_eventuallyEq
    (hl.mono_left nhdsWithin_le_nhds) (hr.mono_left nhdsWithin_le_nhds) he

/-- The interior lift law extends to the closure of the actual current
physical piece, using its angular translation invariance. -/
theorem canonicalChart_periodic_on_closed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K z m) :
    K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) := by
  have hdomains := hA.domains z hz hsector m
  have hcharts := hA.charts z hz hsector m
  have hclosed := (hA.boundary z hz hsector m).2.2.2.2.1
  have hadd : ContinuousAt (fun q : PolarPoint => q + (0, Real.pi)) p :=
    continuousAt_id.add continuousAt_const
  have hpv : p + (0, Real.pi) ∈ physicalPieceClosed S K z m :=
    hadd.continuousWithinAt.mem_closure hp
      (fun q hq => (hdomains.2.2.2.1 q).2 hq)
  exact periodic_lift_at_closure hp
    (hclosed p hp).1.continuousAt (hclosed (p + (0, Real.pi)) hpv).1.continuousAt
    (fun q hq => (hcharts.2.2.2.2.2.2.2 q hq).2.2.1)

/-- A constant radial boundary image and a nonzero actual planar
Jacobian force the actual angular boundary derivative to be nonzero. -/
theorem boundaryAngular_deriv_ne_zero
    {F : PolarPoint → PolarPoint} {c α : ℝ}
    (hF : ∀ θ, DifferentiableAt ℝ F (c, θ))
    (hJ : ∀ θ, planeJacobian F (c, θ) ≠ 0)
    (hradial : ∀ θ, (F (c, θ)).1 = α) :
    ∀ θ, deriv (fun η => (F (c, η)).2) θ ≠ 0 := by
  intro θ hzero
  have hline : HasDerivAt (fun η : ℝ => (c, η)) (0, 1) θ :=
    (hasDerivAt_const θ c).prodMk (hasDerivAt_id' θ)
  have hcurve : HasDerivAt (fun η : ℝ => F (c, η))
      (fderiv ℝ F (c, θ) (0, 1)) θ := by
    simpa only [Function.comp_def] using
      (hF θ).hasFDerivAt.comp_hasDerivAt θ hline
  have hcurve₁ : HasDerivAt (fun η : ℝ => (F (c, η)).1)
      (fderiv ℝ F (c, θ) (0, 1)).1 θ := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      HasFDerivAt.hasDerivAt (HasFDerivAt.fst hcurve.hasFDerivAt)
  have hcurve₂ : HasDerivAt (fun η : ℝ => (F (c, η)).2)
      (fderiv ℝ F (c, θ) (0, 1)).2 θ := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      HasFDerivAt.hasDerivAt (HasFDerivAt.snd hcurve.hasFDerivAt)
  have he : (fun η : ℝ => (F (c, η)).1) = (fun _ : ℝ => α) :=
    funext hradial
  have hξ : (fderiv ℝ F (c, θ) (0, 1)).1 = 0 := by
    have hd : deriv (fun η : ℝ => (F (c, η)).1) θ =
        (fderiv ℝ F (c, θ) (0, 1)).1 := hcurve₁.deriv
    rw [he, deriv_const] at hd
    exact hd.symm
  have hη : (fderiv ℝ F (c, θ) (0, 1)).2 = 0 :=
    hcurve₂.deriv.symm.trans hzero
  apply hJ θ
  simp only [planeJacobian, hξ, hη, mul_zero, zero_mul, sub_zero]

/-- Every true physical circle in the actual closed piece with constant
canonical radial image has a smooth increasing bijective angular lift.
The circle membership is supplied explicitly; it is not inferred from
the reference radial endpoint fields of a moving negative cut. -/
theorem canonicalBoundaryAngular_bijective
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {c α : ℝ}
    (hc : ∀ θ : ℝ, (c, θ) ∈ physicalPieceClosed S K z m)
    (hradial : ∀ θ, (K.chart z m (c, θ)).1 = α) :
    ContDiff ℝ ∞ (fun θ => (K.chart z m (c, θ)).2) ∧
      (∀ θ, 0 < deriv (fun η => (K.chart z m (c, η)).2) θ) ∧
      Function.Bijective (fun θ => (K.chart z m (c, θ)).2) ∧
      (∀ θ, (K.chart z m (c, θ + Real.pi)).2 =
        (K.chart z m (c, θ)).2 + Real.pi) := by
  have hclosed := (hA.boundary z hz hsector m).2.2.2.2.1
  have hf : ContDiff ℝ ∞ (fun θ => (K.chart z m (c, θ)).2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hline : ContDiffAt ℝ ∞ (fun η : ℝ => (c, η)) θ :=
      contDiffAt_const.prodMk contDiffAt_id
    exact ((hclosed (c, θ) (hc θ)).1.comp θ hline).snd
  have hne := boundaryAngular_deriv_ne_zero
    (fun θ => (hclosed (c, θ) (hc θ)).1.differentiableAt (by simp))
    (fun θ => (hclosed (c, θ) (hc θ)).2.2.1) hradial
  have hperiod (θ : ℝ) : (K.chart z m (c, θ + Real.pi)).2 =
      (K.chart z m (c, θ)).2 + Real.pi := by
    simpa only [Prod.mk_add_mk, add_zero, Prod.snd_add] using
      congrArg Prod.snd
        (canonicalChart_periodic_on_closed hA hz hsector m (p := (c, θ)) (hc θ))
  have hpos := deriv_pos_of_periodic_lift_of_ne_zero Real.pi_pos hperiod hne
  exact ⟨hf, hpos, ⟨(strictMono_of_deriv_pos
      (f := fun θ => (K.chart z m (c, θ)).2) hpos).injective,
    surjective_of_continuous_periodic_lift Real.pi_ne_zero hf.continuous hperiod⟩, hperiod⟩

/-- On a positive piece the actual domain contract recovers the original
fixed-rectangle input for a genuine boundary circle. -/
theorem canonicalPositiveBoundaryAngular_bijective
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = true)
    {c α : ℝ} (hc : c ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    (hradial : ∀ θ, (K.chart z m (c, θ)).1 = α) :
    ContDiff ℝ ∞ (fun θ => (K.chart z m (c, θ)).2) ∧
      (∀ θ, 0 < deriv (fun η => (K.chart z m (c, η)).2) θ) ∧
      Function.Bijective (fun θ => (K.chart z m (c, θ)).2) ∧
      (∀ θ, (K.chart z m (c, θ + Real.pi)).2 =
        (K.chart z m (c, θ)).2 + Real.pi) := by
  apply canonicalBoundaryAngular_bijective hA hz hsector m _ hradial
  intro θ
  rw [canonicalPhysicalPieceClosed_of_positive hA hz hsector m hm]
  exact ⟨hc, mem_univ _⟩

end ContinuousFlexibility.Analysis
