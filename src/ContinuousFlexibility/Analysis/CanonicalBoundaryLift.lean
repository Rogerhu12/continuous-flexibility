import ContinuousFlexibility.Analysis.CanonicalBoundaryImage
import ContinuousFlexibility.Analysis.ParameterizedCircleInverse
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Genuine angular lifts on closed canonical boundaries

The interior periodic identity extends to the physical closed strip by
continuity. On a horizontal boundary mapped to a fixed canonical radial
level, the nonzero actual planar Jacobian forces a nonzero angular
derivative. Darboux's theorem and the positive period then force this
derivative to be positive. The resulting genuine boundary angular map is
a bijective degree-one lift; no value of the stored inverse is used.
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
  have hl : ContinuousAt (fun q : PolarPoint => F (q + v)) p :=
    hFv.comp (continuousAt_id.add continuousAt_const)
  have hr : ContinuousAt (fun q : PolarPoint => F q + v) p :=
    hF.add continuousAt_const
  have he : (fun q : PolarPoint => F (q + v)) =ᶠ[𝓝[U] p]
      (fun q : PolarPoint => F q + v) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hperiod q hq
  exact tendsto_nhds_unique_of_eventuallyEq
    (hl.mono_left nhdsWithin_le_nhds) (hr.mono_left nhdsWithin_le_nhds) he

/-- The frozen interior periodicity holds on the actual physical closed
piece by continuity of the forward chart. -/
theorem canonicalChart_periodic_on_closed
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) := by
  have hpiece := hA.2.2.2.1 m
  have hcharts := hA.2.2.2.2.2.2.2.1 z hz hsector m
  have hclosed := hA.2.2.2.2.2.2.2.2.1 z hz hsector m
  have hpv : (p + (0, Real.pi)).1 ∈
      Icc (K.physicalLeft m) (K.physicalRight m) := by
    simpa only [Prod.fst_add, add_zero] using hp
  have hpcl : p ∈ closure (physicalPieceOpen S K m) := by
    rw [physicalPieceOpen, closure_prod_eq, closure_Ioo hpiece.1.ne, closure_univ]
    exact ⟨hp, mem_univ _⟩
  exact periodic_lift_at_closure hpcl
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
  have he : (fun η : ℝ => (F (c, η)).1) = (fun _ : ℝ => α) :=
    funext hradial
  have hξ : (fderiv ℝ F (c, θ) (0, 1)).1 = 0 := by
    have hd : deriv (fun η : ℝ => (F (c, η)).1) θ =
        (fderiv ℝ F (c, θ) (0, 1)).1 := hcurve.fst.deriv
    rw [he, deriv_const] at hd
    exact hd.symm
  have hη : (fderiv ℝ F (c, θ) (0, 1)).2 = 0 :=
    hcurve.snd.deriv.symm.trans hzero
  apply hJ θ
  simp only [planeJacobian, hξ, hη, mul_zero, zero_mul, sub_zero]

/-- Once the radial boundary image has been identified, the forward
boundary angle is a genuine smooth increasing circle lift and bijection.
This applies independently to the root and cut of each half. -/
theorem canonicalBoundaryAngular_bijective
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {c α : ℝ}
    (hc : c ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    (hradial : ∀ θ, (K.chart z m (c, θ)).1 = α) :
    ContDiff ℝ ∞ (fun θ => (K.chart z m (c, θ)).2) ∧
      (∀ θ, 0 < deriv (fun η => (K.chart z m (c, η)).2) θ) ∧
      Function.Bijective (fun θ => (K.chart z m (c, θ)).2) ∧
      (∀ θ, (K.chart z m (c, θ + Real.pi)).2 =
        (K.chart z m (c, θ)).2 + Real.pi) := by
  have hclosed := hA.2.2.2.2.2.2.2.2.1 z hz hsector m
  have hf : ContDiff ℝ ∞ (fun θ => (K.chart z m (c, θ)).2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    have hline : ContDiffAt ℝ ∞ (fun η : ℝ => (c, η)) θ :=
      contDiffAt_const.prodMk contDiffAt_id
    exact ((hclosed (c, θ) hc).1.comp θ hline).snd
  have hne := boundaryAngular_deriv_ne_zero
    (fun θ => (hclosed (c, θ) hc).1.differentiableAt (by simp))
    (fun θ => (hclosed (c, θ) hc).2.2.1) hradial
  have hperiod (θ : ℝ) : (K.chart z m (c, θ + Real.pi)).2 =
      (K.chart z m (c, θ)).2 + Real.pi := by
    simpa only [Prod.mk_add_mk, add_zero, Prod.snd_add] using
      congrArg Prod.snd (canonicalChart_periodic_on_closed hA hz hsector m (p := (c, θ)) hc)
  have hpos := deriv_pos_of_periodic_lift_of_ne_zero Real.pi_pos hperiod hne
  exact ⟨hf, hpos, ⟨(strictMono_of_deriv_pos
      (f := fun θ => (K.chart z m (c, θ)).2) hpos).injective,
    surjective_of_continuous_periodic_lift Real.pi_ne_zero hf.continuous hperiod⟩, hperiod⟩

end ContinuousFlexibility.Analysis
