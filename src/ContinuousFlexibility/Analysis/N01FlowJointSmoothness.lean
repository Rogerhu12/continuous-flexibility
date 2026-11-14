module

public import ContinuousFlexibility.Analysis.CompactParameterIntegral
public import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientRegularity

/-!
# Joint smoothness of the actual N01 flow away from a zero discriminant

The angular variation is already known from the actual ODE. Changing the
base radius in its exponential formula, compact parameter integration
and the radial ODE improve joint Cⁿ regularity to Cⁿ⁺¹. The induction is
local in the open set where the actual characteristic discriminant is
positive; no smoothness of a square root at a turning point is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section ActualSmoothness

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN01 hS hT hz hsector

theorem N01Properties.minusCharacteristicSpeed_contDiffAt_of_discriminant
    {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ContDiffAt ℝ ∞ (minusCharacteristicSpeed (originalCoefficients D S C z)) p := by
  obtain ⟨ha, hb, hc⟩ := hN01.originalCoefficients_contDiffAt hS hT hz hsector hp
  have ha0 := (hN01.originalRadialCoefficient_pos hz hsector hp).ne'
  exact (hb.div ha ha0).sub
    ((((hb.pow 2).sub (ha.mul hc)).sqrt hdisc.ne').div ha ha0)

theorem N01Properties.characteristicAngularDerivative_contDiffAt_of_discriminant
    {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ContDiffAt ℝ ∞ (characteristicAngularDerivative D S C z) p := by
  have hv := hN01.minusCharacteristicSpeed_contDiffAt_of_discriminant hS hT hz hsector hp hdisc
  have hd := contDiffAt_angularPartial hv (m := ∞) (by simp)
  obtain ⟨ha, hb, hc⟩ := hN01.originalCoefficients_contDiffAt hS hT hz hsector hp
  have he : ∀ᶠ q in 𝓝 p, 0 < (originalCoefficients D S C z).b q ^ 2 -
      (originalCoefficients D S C z).a q * (originalCoefficients D S C z).c q :=
    ((hb.pow 2).sub (ha.mul hc)).continuousAt.eventually (Ioi_mem_nhds hdisc)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp, he] with q hq hqdisc
  have hslice := hN01.minusCharacteristicSpeed_hasDerivAt_angular hS hT hz hsector hq.1 q.2
  have hfull := (hN01.minusCharacteristicSpeed_contDiffAt_of_discriminant
    hS hT hz hsector hq hqdisc).differentiableAt (by simp)
  exact hslice.unique (hasDerivAt_angular_slice hfull)

/-- The actual angular variation with an arbitrary interior base radius. -/
theorem N01Properties.minusFlow_angular_deriv_eq_base_mul_exp
    (m : ℕ) {r₀ r : ℝ}
    (h₀ : r₀ ∈ Icc (C.left m) (C.right m))
    (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    deriv (C.minusFlow z m r) θ =
      deriv (C.minusFlow z m r₀) θ *
        Real.exp (∫ s in r₀..r,
          characteristicAngularDerivative D S C z (s, C.minusFlow z m s θ)) := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  let H : PolarPoint → ℝ := fun p =>
    characteristicAngularDerivative D S C z (p.1, C.minusFlow z m p.1 p.2)
  have hH : ContinuousOn H (Icc (C.left m) (C.right m) ×ˢ univ) :=
    (hN01.characteristicAngularDerivative_continuousOn hS hT hz hsector m).comp
      (continuous_fst.continuousOn.prodMk (hN01.minusFlow_continuousOn hz m))
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  let A : ℝ → ℝ := fun s => closedStripExtend (hC.1 m).2.1.le H (s, θ)
  have hA : Continuous A :=
    (continuous_closedStripExtend (hC.1 m).2.1.le hH).comp
      (continuous_id.prodMk continuous_const)
  have hint (a b : ℝ) (ha : a ∈ Icc (C.left m) (C.right m))
      (hb : b ∈ Icc (C.left m) (C.right m)) :
      (∫ s in a..b, characteristicAngularDerivative D S C z
        (s, C.minusFlow z m s θ)) = ∫ s in a..b, A s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (C.left m) (C.right m) :=
      ⟨(le_min ha.1 hb.1).trans hs.1, hs.2.trans (max_le ha.2 hb.2)⟩
    exact (closedStripExtend_eq (hC.1 m).2.1.le H (p := (s, θ)) hs').symm
  have hl : C.left m ∈ Icc (C.left m) (C.right m) := ⟨le_rfl, (hC.1 m).2.1.le⟩
  rw [(hN01.minusFlow_hasDerivAt_exp_integral hS hT hz hsector m hr θ).deriv,
    (hN01.minusFlow_hasDerivAt_exp_integral hS hT hz hsector m h₀ θ).deriv,
    hint _ _ hl hr, hint _ _ hl h₀, hint _ _ h₀ hr, ← Real.exp_add,
    intervalIntegral.integral_add_adjacent_intervals
      (hA.intervalIntegrable (C.left m) r₀) (hA.intervalIntegrable r₀ r)]

theorem N01Properties.minusFlow_contDiffAt_of_discriminant
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : 0 < (originalCoefficients D S C z).b (p.1, C.minusFlow z m p.1 p.2) ^ 2 -
      (originalCoefficients D S C z).a (p.1, C.minusFlow z m p.1 p.2) *
        (originalCoefficients D S C z).c (p.1, C.minusFlow z m p.1 p.2)) :
    ContDiffAt ℝ ∞ (fun q : PolarPoint => C.minusFlow z m q.1 q.2) p := by
  let F : PolarPoint → ℝ := fun q => C.minusFlow z m q.1 q.2
  let δ : PolarPoint → ℝ := fun q =>
    (originalCoefficients D S C z).b (q.1, F q) ^ 2 -
      (originalCoefficients D S C z).a (q.1, F q) *
        (originalCoefficients D S C z).c (q.1, F q)
  let U : Set PolarPoint :=
    (Ioo (C.left m) (C.right m) ×ˢ univ) ∩ {q | 0 < δ q}
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hcore (q : PolarPoint) (hq : q.1 ∈ Ioo (C.left m) (C.right m)) :
      (q.1, F q) ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans hq.1, hq.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hF : ContinuousAt F q :=
      (hN01.minusFlow_hasStrictFDerivAt hS hT hz hsector m q hq.1.1).continuousAt
    obtain ⟨ha, hb, hc⟩ :=
      hN01.originalCoefficients_contDiffAt hS hT hz hsector (hcore q hq.1.1)
    have hδ : ContinuousAt δ q :=
      (((hb.pow 2).sub (ha.mul hc)).continuousAt).comp
        (f := fun y : PolarPoint => (y.1, F y)) (continuousAt_fst.prodMk hF)
    exact inter_mem ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq.1)
      (hδ.eventually (Ioi_mem_nhds hq.2))
  have hpU : p ∈ U := ⟨⟨hp, mem_univ _⟩, hdisc⟩
  let H : PolarPoint → ℝ := fun q =>
    characteristicAngularDerivative D S C z (q.1, F q)
  have hFn : ∀ n : ℕ, ContDiffOn ℝ n F U := by
    intro n
    induction n with
    | zero =>
        apply contDiffOn_zero.mpr
        intro q hq
        exact
          (hN01.minusFlow_hasStrictFDerivAt hS hT hz hsector m q hq.1.1).continuousAt.continuousWithinAt
    | succ n ih =>
        intro q hq
        have harg (x : PolarPoint) (hx : x ∈ U) :
            ContDiffAt ℝ n (fun y : PolarPoint => (y.1, F y)) x :=
          contDiffAt_fst.prodMk (ih.contDiffAt (hU.mem_nhds hx))
        have hHn : ContDiffOn ℝ (n : ℕ∞) H U := by
          intro x hx
          have hd := hN01.characteristicAngularDerivative_contDiffAt_of_discriminant
            hS hT hz hsector (hcore x hx.1.1) hx.2
          exact ((hd.of_le (by simp)).comp x (harg x hx)).contDiffWithinAt
        have hI := contDiffAt_radialPrimitive_of_isOpen hU hq hHn
        have hJ₀ : ContDiff ℝ ∞ (deriv (C.minusFlow z m q.1)) :=
          (contDiff_infty_iff_deriv.mp
            (hN01.minusFlow_angular_contDiff hS hT hz hsector m
              ⟨hq.1.1.1.le, hq.1.1.2.le⟩)).2
        have hJ : ContDiffAt ℝ n
            (fun x : PolarPoint => deriv (C.minusFlow z m x.1) x.2) q := by
          have hbase : ContDiffAt ℝ n
              (fun x : PolarPoint => deriv (C.minusFlow z m q.1) x.2) q :=
            (hJ₀.contDiffAt.of_le (by simp)).comp q contDiffAt_snd
          apply (hbase.mul hI.exp).congr_of_eventuallyEq
          filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hq.1] with x hx
          exact hN01.minusFlow_angular_deriv_eq_base_mul_exp hS hT hz hsector m
            ⟨hq.1.1.1.le, hq.1.1.2.le⟩ ⟨hx.1.1.le, hx.1.2.le⟩ x.2
        have hv : ContDiffAt ℝ n
            (fun x : PolarPoint => minusCharacteristicSpeed (originalCoefficients D S C z)
              (x.1, F x)) q := by
          have hspeed : ContDiffAt ℝ n
              (minusCharacteristicSpeed (originalCoefficients D S C z)) (q.1, F q) :=
            (hN01.minusCharacteristicSpeed_contDiffAt_of_discriminant hS hT hz hsector
              (hcore q hq.1.1) hq.2).of_le (by simp)
          simpa only [Function.comp_def] using hspeed.comp q (harg q hq)
        apply ContDiffAt.contDiffWithinAt
        apply contDiffAt_succ_iff_hasFDerivAt.mpr
        refine ⟨fun x : PolarPoint =>
          minusCharacteristicSpeed (originalCoefficients D S C z) (x.1, F x) •
            ContinuousLinearMap.fst ℝ ℝ ℝ +
          deriv (C.minusFlow z m x.1) x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ,
          ⟨U, hU.mem_nhds hq, ?_⟩,
          (hv.smul contDiffAt_const).add (hJ.smul contDiffAt_const)⟩
        intro x hx
        simpa only [returnFlow_coprod_toSpan] using
          (hN01.minusFlow_hasStrictFDerivAt hS hT hz hsector m x hx.1.1).hasFDerivAt
  exact contDiffAt_infty.mpr fun n => (hFn n).contDiffAt (hU.mem_nhds hpU)

theorem N01Properties.minusFlow_angular_deriv_contDiffAt_of_discriminant
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : 0 < (originalCoefficients D S C z).b (p.1, C.minusFlow z m p.1 p.2) ^ 2 -
      (originalCoefficients D S C z).a (p.1, C.minusFlow z m p.1 p.2) *
        (originalCoefficients D S C z).c (p.1, C.minusFlow z m p.1 p.2)) :
    ContDiffAt ℝ ∞ (fun q : PolarPoint => deriv (C.minusFlow z m q.1) q.2) p := by
  have hF := hN01.minusFlow_contDiffAt_of_discriminant hS hT hz hsector m p hp hdisc
  apply (contDiffAt_angularPartial hF (m := ∞) (by simp)).congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
    (show p ∈ Ioo (C.left m) (C.right m) ×ˢ univ from ⟨hp, mem_univ _⟩)] with q hq
  exact (hasDerivAt_angular_slice
    (hN01.minusFlow_hasStrictFDerivAt hS hT hz hsector m q hq.1).hasFDerivAt.differentiableAt).deriv

theorem N01Properties.minusFlow_invFun_contDiffAt_of_discriminant
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ContDiffAt ℝ ∞ (fun q : PolarPoint => Function.invFun (C.minusFlow z m q.1) q.2) p := by
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  have hclosed : p.1 ∈ Icc (C.left m) (C.right m) := ⟨hp.1.le, hp.2.le⟩
  have hsurj := returnLift_surjective Real.pi_pos
    (N01Properties.minusFlow_differentiable S C z m hN01 hz hclosed).continuous
    (hN01.minusFlow_add_period hz m hclosed)
  let α := Function.invFun (C.minusFlow z m p.1) p.2
  have hpoint : (p.1, C.minusFlow z m p.1 α) = p := by
    apply Prod.ext
    · rfl
    · exact Function.rightInverse_invFun hsurj p.2
  have hdisc' : 0 < (originalCoefficients D S C z).b (p.1, C.minusFlow z m p.1 α) ^ 2 -
      (originalCoefficients D S C z).a (p.1, C.minusFlow z m p.1 α) *
        (originalCoefficients D S C z).c (p.1, C.minusFlow z m p.1 α) := by
    rw [hpoint]
    exact hdisc
  have hinj : ∀ᶠ r in 𝓝 p.1, Function.Injective (C.minusFlow z m r) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with r hr
    exact (strictMono_of_deriv_pos fun θ =>
      ((hflow z hz m θ).2.2.2 r ⟨hr.1.le, hr.2.le⟩).1).injective
  have h := returnFlow_invFun_contDiffAt
    (hN01.minusFlow_contDiffAt_of_discriminant hS hT hz hsector m (p.1, α) hp hdisc')
    (by simp) (((hflow z hz m α).2.2.2 p.1 hclosed).1.ne') hinj
  rw [hpoint] at h
  exact h

end ActualSmoothness

end ContinuousFlexibility.Statements
