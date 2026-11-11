import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Tests and closed weak differentiation on the material cylinder

All mixed derivatives preserve the actual cylinder test space, including
the radial support bound. The integral identities defining weak mixed
derivatives are kernels of continuous linear functionals on the actual
pair of cylinder `L²` spaces.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace InnerProductSpace

/-- Every mixed derivative vanishes outside the same radial support bound,
including the boundary circles. -/
theorem mixedDerivative_zero_of_radial_support {φ : PolarPoint → ℝ} {R : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hzero : ∀ p : PolarPoint, R ≤ |p.1| → φ p = 0)
    (a b : ℕ) (p : PolarPoint) (hp : R ≤ |p.1|) : mixedDerivative a b φ p = 0 := by
  have hstrict (q : PolarPoint) (hq : R < |q.1|) : mixedDerivative a b φ q = 0 := by
    have hnear : ∀ᶠ s : ℝ in 𝓝 q.1, R < |s| :=
      continuousAt_const.eventually_lt continuous_abs.continuousAt hq
    have he : (fun s : ℝ => iteratedDeriv b (fun t : ℝ => φ (s, t)) q.2) =ᶠ[𝓝 q.1]
        (0 : ℝ → ℝ) := by
      filter_upwards [hnear] with s hs
      have hz : (fun t : ℝ => φ (s, t)) = (0 : ℝ → ℝ) :=
        funext (fun t => hzero (s, t) hs.le)
      simp only [hz, iteratedDeriv_const_zero, Pi.zero_apply]
    simpa only [mixedDerivative, iteratedDeriv_const_zero, Pi.zero_apply] using he.iteratedDeriv_eq a
  let g (s : ℝ) := mixedDerivative a b φ (s, p.2)
  have hg : Continuous g :=
    (contDiff_mixedDerivative hφ a b).continuous.comp (continuous_id.prodMk continuous_const)
  have hc : IsClosed {s : ℝ | g s = 0} := isClosed_eq hg continuous_const
  change g p.1 = 0
  by_cases hs : 0 ≤ p.1
  · have ho : Ioi R ⊆ {s : ℝ | g s = 0} := by
      intro s hs'
      exact hstrict (s, p.2) ((show R < s from hs').trans_le (le_abs_self s))
    apply closure_minimal ho hc
    rw [closure_Ioi]
    simpa only [mem_Ici, abs_of_nonneg hs] using hp
  · have ho : Iio (-R) ⊆ {s : ℝ | g s = 0} := by
      intro s hs'
      have h : R < -s := by linarith only [show s < -R from hs']
      exact hstrict (s, p.2) (h.trans_le (neg_le_abs s))
    apply closure_minimal ho hc
    rw [closure_Iio]
    have h : R ≤ -p.1 := by simpa only [abs_of_nonpos (le_of_not_ge hs)] using hp
    change p.1 ≤ -R
    linarith only [h]

theorem IsCylinderTest.mixedDerivative {φ : PolarPoint → ℝ} (hφ : IsCylinderTest φ) (a b : ℕ) :
    IsCylinderTest (Statements.mixedDerivative a b φ) := by
  obtain ⟨R, hR, hzero⟩ := hφ.2.2
  refine ⟨contDiff_mixedDerivative hφ.1 a b, ?_, R, hR,
    mixedDerivative_zero_of_radial_support hφ.1 hzero a b⟩
  have hper (x : ℝ) : Function.Periodic (fun θ : ℝ => φ (x, θ)) Real.pi := by
    intro θ
    have h := hφ.2.1 (x, θ)
    change φ (x + 0, θ + Real.pi) = φ (x, θ) at h
    simpa only [add_zero] using h
  intro p
  change Statements.mixedDerivative a b φ (p.1 + 0, p.2 + Real.pi) =
    Statements.mixedDerivative a b φ (p.1, p.2)
  rw [add_zero]
  exact mixedDerivative_angular_periodic hper a b p.1 p.2

/-- A test is square-integrable for the actual cylinder measure. -/
theorem IsCylinderTest.memLp {φ : PolarPoint → ℝ} (hφ : IsCylinderTest φ) :
    MemLp φ 2 materialCylinderMeasure := by
  obtain ⟨R, _, hzero⟩ := hφ.2.2
  let K : Set PolarPoint := Icc (-R) R ×ˢ Icc 0 Real.pi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  let : IsFiniteMeasureOnCompacts materialCylinderMeasure := by
    unfold materialCylinderMeasure
    infer_instance
  let : IsFiniteMeasure (materialCylinderMeasure.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hK.bddAbove_image hφ.1.continuous.norm.continuousOn
  have hLp : MemLp φ 2 (materialCylinderMeasure.restrict K) :=
    MemLp.of_bound hφ.1.continuous.aestronglyMeasurable M <|
      (ae_restrict_mem hKm).mono (fun p hp => hM ⟨p, hp, rfl⟩)
  have hI : MemLp (K.indicator φ) 2 materialCylinderMeasure :=
    (memLp_indicator_iff_restrict hKm).mpr hLp
  have hstrip : ∀ᵐ p ∂materialCylinderMeasure, p.2 ∈ Ioc (0 : ℝ) Real.pi :=
    (ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)).mono (fun p hp => hp.2)
  apply MemLp.ae_eq _ hI
  filter_upwards [hstrip] with p hp
  by_cases hpK : p ∈ K
  · exact Set.indicator_of_mem hpK _
  · have hlarge : R ≤ |p.1| := (lt_of_not_ge (fun hsmall =>
      hpK ⟨abs_le.mp hsmall, Ioc_subset_Icc_self hp⟩)).le
    rw [Set.indicator_of_notMem hpK, hzero p hlarge]

theorem IsCylinderTest.mixedDerivative_memLp {φ : PolarPoint → ℝ} (hφ : IsCylinderTest φ)
    (a b : ℕ) : MemLp (Statements.mixedDerivative a b φ) 2 materialCylinderMeasure :=
  (hφ.mixedDerivative a b).memLp

/-- The integral pairing with any actual square-integrable cylinder function. -/
def cylinderTestPairing (φ : PolarPoint → ℝ) (hφ : MemLp φ 2 materialCylinderMeasure) :
    CylinderL2 →L[ℝ] ℝ := innerSL ℝ (hφ.toLp φ)

theorem cylinderTestPairing_apply (φ : PolarPoint → ℝ) (hφ : MemLp φ 2 materialCylinderMeasure)
    (u : CylinderL2) : cylinderTestPairing φ hφ u = ∫ p, u p * φ p ∂materialCylinderMeasure := by
  change ⟪hφ.toLp φ, u⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hφ] with p hp
  rw [hp]
  simp only [RCLike.inner_apply, conj_trivial]

def cylinderWeakTestResidual (a b : ℕ) (φ : PolarPoint → ℝ) (hφ : IsCylinderTest φ) :
    (CylinderL2 × CylinderL2) →L[ℝ] ℝ :=
  (cylinderTestPairing φ hφ.memLp).comp (ContinuousLinearMap.snd ℝ CylinderL2 CylinderL2) -
    (-1 : ℝ) ^ (a + b) •
      (cylinderTestPairing (mixedDerivative a b φ) (IsCylinderTest.mixedDerivative_memLp hφ a b)).comp
        (ContinuousLinearMap.fst ℝ CylinderL2 CylinderL2)

theorem cylinderWeakTestResidual_apply (a b : ℕ) (φ : PolarPoint → ℝ) (hφ : IsCylinderTest φ)
    (z : CylinderL2 × CylinderL2) :
    cylinderWeakTestResidual a b φ hφ z = (∫ p, z.2 p * φ p ∂materialCylinderMeasure) -
      (-1 : ℝ) ^ (a + b) * ∫ p, z.1 p * mixedDerivative a b φ p ∂materialCylinderMeasure := by
  change cylinderTestPairing φ hφ.memLp z.2 - (-1 : ℝ) ^ (a + b) *
    cylinderTestPairing (mixedDerivative a b φ) (IsCylinderTest.mixedDerivative_memLp hφ a b) z.1 = _
  rw [cylinderTestPairing_apply, cylinderTestPairing_apply]

/-- The weak mixed derivative relation on the unweighted cylinder pair. -/
def weakMixedDerivativeGraph (a b : ℕ) : Submodule ℝ (CylinderL2 × CylinderL2) :=
  ⨅ φ : {φ : PolarPoint → ℝ // IsCylinderTest φ}, (cylinderWeakTestResidual a b φ.val φ.prop).ker

theorem mem_weakMixedDerivativeGraph (a b : ℕ) (z : CylinderL2 × CylinderL2) :
    z ∈ weakMixedDerivativeGraph a b ↔ HasWeakMixedDerivative z.1 z.2 a b := by
  simp only [weakMixedDerivativeGraph, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, cylinderWeakTestResidual_apply, sub_eq_zero]
  exact ⟨fun h φ hφ => h ⟨φ, hφ⟩, fun h φ => h φ.val φ.prop⟩

theorem isClosed_weakMixedDerivativeGraph (a b : ℕ) :
    IsClosed (weakMixedDerivativeGraph a b : Set (CylinderL2 × CylinderL2)) := by
  rw [weakMixedDerivativeGraph, Submodule.coe_iInf]
  exact isClosed_iInter (fun φ => (cylinderWeakTestResidual a b φ.val φ.prop).isClosed_ker)

theorem isClosed_hasWeakMixedDerivative (a b : ℕ) :
    IsClosed {z : CylinderL2 × CylinderL2 | HasWeakMixedDerivative z.1 z.2 a b} := by
  have h : (weakMixedDerivativeGraph a b : Set (CylinderL2 × CylinderL2)) =
      {z | HasWeakMixedDerivative z.1 z.2 a b} := Set.ext (mem_weakMixedDerivativeGraph a b)
  rw [← h]
  exact isClosed_weakMixedDerivativeGraph a b

theorem materialCylinderMeasure_eq_prod :
    materialCylinderMeasure = (volume : Measure ℝ).prod angleMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioc 0 Real.pi) =
    (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioc 0 Real.pi))
  rw [← Measure.prod_restrict, Measure.restrict_univ]

theorem measurePreserving_angleReflection :
    MeasurePreserving (fun θ : ℝ => Real.pi - θ) angleMeasure angleMeasure := by
  have hv : MeasurePreserving (fun θ : ℝ => Real.pi - θ) volume volume :=
    (volume : Measure ℝ).measurePreserving_sub_left Real.pi
  have hpre : (fun θ : ℝ => Real.pi - θ) ⁻¹' Ioc 0 Real.pi = Ico 0 Real.pi := by
    ext θ
    change (0 < Real.pi - θ ∧ Real.pi - θ ≤ Real.pi) ↔ (0 ≤ θ ∧ θ < Real.pi)
    constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
  have hnull : (Ico 0 Real.pi : Set ℝ) =ᵐ[(volume : Measure ℝ)] Ioc 0 Real.pi :=
    Ico_ae_eq_Icc.trans Ioc_ae_eq_Icc.symm
  have h := hv.restrict_preimage (s := Ioc 0 Real.pi) measurableSet_Ioc
  rw [hpre, Measure.restrict_congr_set hnull] at h
  exact h

def cylinderAngularReflection (p : PolarPoint) : PolarPoint := (p.1, Real.pi - p.2)

theorem measurePreserving_cylinderAngularReflection :
    MeasurePreserving cylinderAngularReflection materialCylinderMeasure materialCylinderMeasure := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  rw [materialCylinderMeasure_eq_prod]
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod measurePreserving_angleReflection

def cylinderReflectionL2 : CylinderL2 →ₗᵢ[ℝ] CylinderL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ cylinderAngularReflection measurePreserving_cylinderAngularReflection

theorem cylinderReflectionL2_ae (u : CylinderL2) :
    (cylinderReflectionL2 u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (fun p => u (p.1, Real.pi - p.2)) :=
  Lp.coeFn_compMeasurePreserving u measurePreserving_cylinderAngularReflection

theorem cylinderReflectionL2_fixed_iff (u : CylinderL2) : cylinderReflectionL2 u = u ↔
    (fun p : PolarPoint => u (p.1, Real.pi - p.2)) =ᵐ[materialCylinderMeasure] (u : PolarPoint → ℝ) := by
  constructor
  · intro h
    have he := cylinderReflectionL2_ae u
    rw [h] at he
    exact he.symm
  · intro h
    exact Lp.ext ((cylinderReflectionL2_ae u).trans h)

theorem isClosed_cylinderReflection_fixed :
    IsClosed {u : CylinderL2 | cylinderReflectionL2 u = u} :=
  isClosed_eq cylinderReflectionL2.continuous continuous_id

end ContinuousFlexibility.Statements
