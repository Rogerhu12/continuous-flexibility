import ContinuousFlexibility.Analysis.N01FlowChartIndependence
import ContinuousFlexibility.Analysis.N01FlowContinuity
import ContinuousFlexibility.Analysis.ScalarFlowVariation

/-!
# The actual N01 angular variational equation

All coefficients below are computed from the original nonlinear data.
Their smooth angular factors and continuous radial square root supply the
closed-strip hypotheses of the scalar variational equation.  In particular
the actual return at the right turning radius has a continuous angular
derivative given by an exponential integral.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def stateCharacteristicDrift (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) : ℝ :=
  (originalCoefficients D S C z).b p / (originalCoefficients D S C z).a p

def characteristicAngularFactor (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) : ℝ :=
  1 / (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p *
    (originalCoefficients D S C z).a p)

def characteristicRadialRoot (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (r : ℝ) : ℝ :=
  Real.sqrt (-(stateProfile D S C z.1 r * deriv (stateProfile D S C z.1) r / r))

def characteristicAngularDerivative (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) : ℝ :=
  angularPartial (stateCharacteristicDrift D S C z) p - characteristicRadialRoot D S C z p.1 *
    angularPartial (characteristicAngularFactor D S C z) p

section ActualRegularity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN01 hS hT hz hsector

theorem N01Properties.characteristic_factors_contDiffAt
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (stateCharacteristicDrift D S C z) p ∧
    ContDiffAt ℝ ∞ (characteristicAngularFactor D S C z) p := by
  obtain ⟨ha, hD, _, hA, hB, hDreg⟩ :=
    N01Properties.characteristic_coefficient_regular hN01 hS hT hz hsector hp
  exact ⟨hB.div hA ha.ne', contDiffAt_const.div (hDreg.mul hA) (mul_ne_zero hD.ne' ha.ne')⟩

omit hz hsector in
theorem N01Properties.characteristicRadialRoot_continuousAt
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    ContinuousAt (characteristicRadialRoot D S C z) r := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  obtain ⟨_, hgeom⟩ := hN01.1.1
  have hr0 : r ≠ 0 := (hgeom.1.1.trans hr.1).ne'
  exact ((hw.continuous.continuousAt.mul (hw.continuous_deriv (by simp)).continuousAt).div
    continuousAt_id hr0).neg.sqrt

theorem N01Properties.minusCharacteristicSpeed_eq_separated
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    minusCharacteristicSpeed (originalCoefficients D S C z) p =
      stateCharacteristicDrift D S C z p - characteristicRadialRoot D S C z p.1 *
        characteristicAngularFactor D S C z p := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  obtain ⟨_, hgeom⟩ := hN01.1.1
  have hr0 : p.1 ≠ 0 := (hgeom.1.1.trans hp.1.1).ne'
  obtain ⟨_, hD, hQ, _⟩ :=
    N01Properties.characteristic_coefficient_regular hN01 hS hT hz hsector hp
  exact minusCharacteristicSpeed_separated (hw.differentiable (by simp) p.1) hr0 hD hQ

theorem N01Properties.minusCharacteristicSpeed_hasDerivAt_angular
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (θ : ℝ) :
    HasDerivAt (fun t => minusCharacteristicSpeed (originalCoefficients D S C z) (r, t))
      (characteristicAngularDerivative D S C z (r, θ)) θ := by
  obtain ⟨hA, hB⟩ := N01Properties.characteristic_factors_contDiffAt hN01 hS hT hz hsector
    (p := (r, θ)) ⟨hr, mem_univ _⟩
  have h := (hasDerivAt_angular_slice (hA.differentiableAt (by simp))).sub
    ((hasDerivAt_angular_slice (hB.differentiableAt (by simp))).const_mul
      (characteristicRadialRoot D S C z r))
  apply h.congr_of_eventuallyEq
  exact Eventually.of_forall fun t => by
    simpa only [Pi.sub_apply, Pi.mul_apply] using
      N01Properties.minusCharacteristicSpeed_eq_separated hN01 hS hT hz hsector
        (p := (r, t)) ⟨hr, mem_univ _⟩

theorem N01Properties.characteristicAngularDerivative_continuousOn
    (m : ℕ) : ContinuousOn (characteristicAngularDerivative D S C z)
      (Icc (C.left m) (C.right m) ×ˢ univ) := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hcore {p : PolarPoint} (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
      p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans_le hp.1, hp.2.trans_lt (hcontrol.1 m).2.2⟩, mem_univ _⟩
  intro p hp
  obtain ⟨hA, hB⟩ := N01Properties.characteristic_factors_contDiffAt hN01 hS hT hz hsector
    (hcore (p := p) hp.1)
  have hAθ := (contDiffAt_angularPartial hA (m := ∞) (by simp)).continuousAt
  have hBθ := (contDiffAt_angularPartial hB (m := ∞) (by simp)).continuousAt
  have hk := (N01Properties.characteristicRadialRoot_continuousAt hN01 hS hT
    (z := z) (hcore (p := p) hp.1).1).comp continuousAt_fst
  exact (hAθ.sub (hk.mul hBθ)).continuousWithinAt

end ActualRegularity

section ActualFlow

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1) (m : ℕ)

include hN01 hS hT hz hsector

/-- The actual first angular variation, valid at the right return radius
as well as in the interior. -/
theorem N01Properties.minusFlow_hasDerivAt_exp_integral
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    HasDerivAt (C.minusFlow z m r)
      (Real.exp (∫ s in C.left m..r,
        characteristicAngularDerivative D S C z (s, C.minusFlow z m s θ))) θ := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  apply Analysis.scalar_flow_hasDerivAt_exp_integral_on
    (v := fun s x => minusCharacteristicSpeed (originalCoefficients D S C z) (s, x))
    (d := fun s x => characteristicAngularDerivative D S C z (s, x))
    (hcontrol.1 m).2.1
    (N01Properties.characteristicAngularDerivative_continuousOn hN01 hS hT hz hsector m)
    (fun s hs x => N01Properties.minusCharacteristicSpeed_hasDerivAt_angular
      hN01 hS hT hz hsector
      ⟨(hcontrol.1 m).1.trans_le hs.1, hs.2.trans_lt (hcontrol.1 m).2.2⟩ x)
    (N01Properties.minusFlow_continuousOn hN01 hz m)
    (fun x => (hflow z hz m x).1)
    (fun x s hs => (hflow z hz m x).2.2.1 s hs) hr θ

theorem N01Properties.minusFlow_angular_deriv_continuousOn :
    ContinuousOn (fun p : PolarPoint => deriv (C.minusFlow z m p.1) p.2)
      (Icc (C.left m) (C.right m) ×ˢ univ) := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  exact Analysis.scalar_flow_angular_deriv_continuousOn
    (v := fun s x => minusCharacteristicSpeed (originalCoefficients D S C z) (s, x))
    (d := fun s x => characteristicAngularDerivative D S C z (s, x))
    (hcontrol.1 m).2.1
    (N01Properties.characteristicAngularDerivative_continuousOn hN01 hS hT hz hsector m)
    (fun s hs x => N01Properties.minusCharacteristicSpeed_hasDerivAt_angular
      hN01 hS hT hz hsector
      ⟨(hcontrol.1 m).1.trans_le hs.1, hs.2.trans_lt (hcontrol.1 m).2.2⟩ x)
    (N01Properties.minusFlow_continuousOn hN01 hz m)
    (fun x => (hflow z hz m x).1)
    (fun x s hs => (hflow z hz m x).2.2.1 s hs)

theorem N01Properties.minusFlow_angular_contDiff_one
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    ContDiff ℝ 1 (C.minusFlow z m r) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨N01Properties.minusFlow_differentiable S C z m hN01 hz hr, ?_⟩
  have hdc := N01Properties.minusFlow_angular_deriv_continuousOn hN01 hS hT hz hsector m
  exact (hdc.comp_continuous (continuous_const.prodMk continuous_id)
    (fun θ => ⟨hr, mem_univ _⟩)).congr fun θ => rfl

end ActualFlow

end ContinuousFlexibility.Statements
