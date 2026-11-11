import ContinuousFlexibility.Statements.Radial
import ContinuousFlexibility.Radial.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Full Liouville transport on the actual open radius range

No endpoint or surjectivity condition on the positive increasing radius is
imposed. The primitive is integrated in model coordinates, and multiplication
by the possibly unbounded positive density is implemented by changing measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

def generalLiouvilleCoordinate (R : ℝ → ℝ) : ℝ → ℝ := Function.invFun R

def generalLiouvilleProfile (R s : ℝ → ℝ) (scale r : ℝ) : ℝ :=
  scale * s (generalLiouvilleCoordinate R r) ^ 2 *
    deriv R (generalLiouvilleCoordinate R r)

def generalLiouvillePrimitiveIntegrand (R s : ℝ → ℝ) (scale x : ℝ) : ℝ :=
  scale * s x ^ 2 * deriv R x ^ 2

def generalLiouvilleModelPrimitive (R s : ℝ → ℝ) (scale x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, generalLiouvillePrimitiveIntegrand R s scale t

def generalLiouvillePrimitive (R s : ℝ → ℝ) (scale r : ℝ) : ℝ :=
  generalLiouvilleModelPrimitive R s scale (generalLiouvilleCoordinate R r)

variable {R s : ℝ → ℝ} {scale : ℝ}

theorem generalLiouville_strictMono (hd : ∀ x, 0 < deriv R x) : StrictMono R :=
  strictMono_of_deriv_pos hd

theorem generalLiouvilleCoordinate_apply (hd : ∀ x, 0 < deriv R x) (x : ℝ) :
    generalLiouvilleCoordinate R (R x) = x :=
  Function.leftInverse_invFun (generalLiouville_strictMono hd).injective x

theorem generalLiouvilleCoordinate_right {r : ℝ} (hr : r ∈ range R) :
    R (generalLiouvilleCoordinate R r) = r :=
  Function.invFun_eq hr

theorem generalLiouvilleCoordinate_hasStrictDerivAt
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) (x : ℝ) :
    HasStrictDerivAt (generalLiouvilleCoordinate R) (deriv R x)⁻¹ (R x) :=
  (hR.hasStrictDerivAt (x := x) (by simp)).to_local_left_inverse (hd x).ne'
    (Eventually.of_forall (generalLiouvilleCoordinate_apply hd))

theorem generalLiouvilleCoordinate_contDiffAt
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) (x : ℝ) :
    ContDiffAt ℝ ∞ (generalLiouvilleCoordinate R) (R x) := by
  have h0 := (hd x).ne'
  let h := (hR.hasStrictDerivAt (x := x) (by simp)).hasStrictFDerivAt_equiv h0
  let e := h.toOpenPartialHomeomorph R
  have he : e.symm (R x) = x := h.localInverse_apply_image
  have hD : HasDerivAt e (deriv R x) (e.symm (R x)) := by
    rw [he]
    exact (hR.differentiable (by simp) x).hasDerivAt
  have hC : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm (R x)) := by
    rw [he]
    exact hR.contDiffAt
  have hi := e.contDiffAt_symm_deriv h0 h.image_mem_toOpenPartialHomeomorph_target hD hC
  have heq : generalLiouvilleCoordinate R =ᶠ[𝓝 (R x)] (e.symm : ℝ → ℝ) :=
    h.localInverse_unique (Eventually.of_forall (generalLiouvilleCoordinate_apply hd))
  exact hi.congr_of_eventuallyEq heq

theorem generalLiouville_isOpenEmbedding
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) :
    Topology.IsOpenEmbedding R :=
  Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨hR.continuous, (generalLiouville_strictMono hd).injective,
      isOpenMap_of_hasStrictDerivAt (fun x => hR.hasStrictDerivAt (x := x) (by simp))
        (fun x => (hd x).ne')⟩

theorem generalLiouville_measurableEmbedding
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) :
    MeasurableEmbedding R :=
  (generalLiouville_isOpenEmbedding hR hd).measurableEmbedding

theorem generalLiouvilleProfile_apply (hd : ∀ x, 0 < deriv R x) (x : ℝ) :
    generalLiouvilleProfile R s scale (R x) = scale * s x ^ 2 * deriv R x := by
  simp only [generalLiouvilleProfile, generalLiouvilleCoordinate_apply hd]

theorem generalLiouvilleProfile_contDiffAt
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hd : ∀ x, 0 < deriv R x) (x : ℝ) :
    ContDiffAt ℝ ∞ (generalLiouvilleProfile R s scale) (R x) :=
  ((contDiff_const.mul (hs.pow 2)).mul (contDiff_infty_iff_deriv.mp hR).2).contDiffAt.comp
    _ (generalLiouvilleCoordinate_contDiffAt hR hd x)

theorem generalLiouvillePrimitiveIntegrand_contDiff
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s) :
    ContDiff ℝ ∞ (generalLiouvillePrimitiveIntegrand R s scale) :=
  (contDiff_const.mul (hs.pow 2)).mul ((contDiff_infty_iff_deriv.mp hR).2.pow 2)

theorem generalLiouvilleModelPrimitive_hasDerivAt
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s) (x : ℝ) :
    HasDerivAt (generalLiouvilleModelPrimitive R s scale)
      (generalLiouvillePrimitiveIntegrand R s scale x) x := by
  have hc := (generalLiouvillePrimitiveIntegrand_contDiff hR hs (scale := scale)).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem generalLiouvilleModelPrimitive_contDiff
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s) :
    ContDiff ℝ ∞ (generalLiouvilleModelPrimitive R s scale) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (generalLiouvilleModelPrimitive_hasDerivAt hR hs x).differentiableAt, ?_⟩
  have heq : deriv (generalLiouvilleModelPrimitive R s scale) =
      generalLiouvillePrimitiveIntegrand R s scale :=
    funext (fun x => (generalLiouvilleModelPrimitive_hasDerivAt hR hs x).deriv)
  rw [heq]
  exact generalLiouvillePrimitiveIntegrand_contDiff hR hs

theorem generalLiouvillePrimitive_contDiffAt
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hd : ∀ x, 0 < deriv R x) (x : ℝ) :
    ContDiffAt ℝ ∞ (generalLiouvillePrimitive R s scale) (R x) :=
  (generalLiouvilleModelPrimitive_contDiff hR hs).contDiffAt.comp
    _ (generalLiouvilleCoordinate_contDiffAt hR hd x)

theorem generalLiouvillePrimitive_hasDerivAt
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hd : ∀ x, 0 < deriv R x) (x : ℝ) :
    HasDerivAt (generalLiouvillePrimitive R s scale)
      (generalLiouvilleProfile R s scale (R x)) (R x) := by
  have hi := (generalLiouvilleCoordinate_hasStrictDerivAt hR hd x).hasDerivAt
  have hp := (generalLiouvilleModelPrimitive_hasDerivAt (scale := scale) hR hs x).comp_of_eq (R x) hi
    (generalLiouvilleCoordinate_apply hd x).symm
  change HasDerivAt (generalLiouvillePrimitive R s scale)
    (generalLiouvillePrimitiveIntegrand R s scale x * (deriv R x)⁻¹) (R x) at hp
  have hv : generalLiouvillePrimitiveIntegrand R s scale x * (deriv R x)⁻¹ =
      generalLiouvilleProfile R s scale (R x) := by
    rw [generalLiouvilleProfile_apply hd]
    unfold generalLiouvillePrimitiveIntegrand
    field_simp [(hd x).ne']
  rwa [hv] at hp

theorem generalLiouville_radialJacobi
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
    {ψ u : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hu : ContDiff ℝ ∞ u)
    (hheight : ∀ x, u (R x) = ψ x / s x) (j x : ℝ) :
    radialJacobi (j ^ 2) (generalLiouvilleProfile R s scale) u (R x) =
      -(scale * s x / deriv R x) * liouvilleSchrodinger (j ^ 2) R s ψ x := by
  have hd := fun x => (hp x).2.1
  have hw := (generalLiouvilleProfile_contDiffAt (scale := scale) hR hs hd x).differentiableAt (by simp)
  exact radialJacobi_liouville
    (Eventually.of_forall (hR.differentiable (by simp)))
    (Eventually.of_forall (hs.differentiable (by simp)))
    (Eventually.of_forall (hψ.differentiable (by simp)))
    (Eventually.of_forall (fun t => hu.differentiable (by simp) (R t)))
    ((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) x)
    ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp) x)
    ((contDiff_infty_iff_deriv.mp hψ).2.differentiable (by simp) x) hw
    (hw.mul ((contDiff_infty_iff_deriv.mp hu).2.differentiable (by simp) (R x)))
    (hp x).1.ne' (hp x).2.1.ne' (hp x).2.2.ne'
    (Eventually.of_forall (generalLiouvilleProfile_apply hd))
    (Eventually.of_forall hheight)

def generalLiouvilleModelDensity (R : ℝ → ℝ) (scale x : ℝ) : ℝ :=
  12 * scale * (deriv R x / R x) ^ 2

def generalLiouvillePhysicalDensity (R s : ℝ → ℝ) (scale r : ℝ) : ℝ :=
  12 * generalLiouvilleProfile R s scale r / r ^ 2

def generalLiouvilleModelMeasure (R : ℝ → ℝ) (scale : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (generalLiouvilleModelDensity R scale x))

def generalLiouvillePhysicalMeasure (R s : ℝ → ℝ) (scale : ℝ) : Measure ℝ :=
  (volume.restrict (range R)).withDensity
    (fun r => ENNReal.ofReal (generalLiouvillePhysicalDensity R s scale r))

def generalLiouvillePullbackDensity (R s : ℝ → ℝ) (scale x : ℝ) : ℝ :=
  generalLiouvilleModelDensity R scale x * s x ^ 2

def generalLiouvillePullbackMeasure (R s : ℝ → ℝ) (scale : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (generalLiouvillePullbackDensity R s scale x))

abbrev GeneralLiouvilleModelL2 (R : ℝ → ℝ) (scale : ℝ) :=
  Lp ℝ 2 (generalLiouvilleModelMeasure R scale)

abbrev GeneralLiouvillePhysicalL2 (R s : ℝ → ℝ) (scale : ℝ) :=
  Lp ℝ 2 (generalLiouvillePhysicalMeasure R s scale)

theorem generalLiouvilleModelDensity_continuous
    (hR : ContDiff ℝ ∞ R) (hpos : ∀ x, 0 < R x) :
    Continuous (generalLiouvilleModelDensity R scale) :=
  continuous_const.mul (((contDiff_infty_iff_deriv.mp hR).2.continuous.div
    hR.continuous (fun x => (hpos x).ne')).pow 2)

theorem generalLiouville_density (hd : ∀ x, 0 < deriv R x)
    (hpos : ∀ x, 0 < R x) (x : ℝ) :
    deriv R x * generalLiouvillePhysicalDensity R s scale (R x) =
      generalLiouvillePullbackDensity R s scale x := by
  unfold generalLiouvillePhysicalDensity generalLiouvillePullbackDensity generalLiouvilleModelDensity
  rw [generalLiouvilleProfile_apply hd]
  field_simp [(hpos x).ne']

theorem generalLiouville_lintegral_change
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) (g : ℝ → ℝ≥0∞) :
    (∫⁻ r in range R, g r) = ∫⁻ x, ENNReal.ofReal (deriv R x) * g (R x) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (hR.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
    (generalLiouville_strictMono hd).injective.injOn g
  simpa only [image_univ, Measure.restrict_univ, abs_of_pos (hd _)] using h

theorem generalLiouville_integrable_iff
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) (g : ℝ → ℝ) :
    IntegrableOn g (range R) ↔ Integrable (fun x => deriv R x * g (R x)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hR.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
    (generalLiouville_strictMono hd).injective.injOn g
  simpa only [image_univ, IntegrableOn, Measure.restrict_univ,
    abs_of_pos (hd _), smul_eq_mul] using h

theorem generalLiouville_integral_change
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) (g : ℝ → ℝ) :
    (∫ r in range R, g r) = ∫ x, deriv R x * g (R x) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hR.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
    (generalLiouville_strictMono hd).injective.injOn g
  simpa only [image_univ, Measure.restrict_univ, abs_of_pos (hd _), smul_eq_mul] using h

theorem generalLiouville_map_measure
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) (hpos : ∀ x, 0 < R x) :
    Measure.map R (generalLiouvillePullbackMeasure R s scale) =
      generalLiouvillePhysicalMeasure R s scale := by
  ext t ht
  have hpre := hR.continuous.measurable ht
  rw [Measure.map_apply hR.continuous.measurable ht,
    generalLiouvillePullbackMeasure, withDensity_apply _ hpre]
  calc
    _ = ∫⁻ x, (R ⁻¹' t).indicator
        (fun x => ENNReal.ofReal (generalLiouvillePullbackDensity R s scale x)) x :=
      (lintegral_indicator hpre _).symm
    _ = ∫⁻ x, ENNReal.ofReal (deriv R x) *
        t.indicator (fun r => ENNReal.ofReal (generalLiouvillePhysicalDensity R s scale r))
          (R x) := by
      apply lintegral_congr
      intro x
      by_cases hx : R x ∈ t
      · simp only [mem_preimage, hx, indicator_of_mem]
        rw [← ENNReal.ofReal_mul (hd x).le, generalLiouville_density hd hpos]
      · simp [hx]
    _ = ∫⁻ r in range R,
        t.indicator (fun r => ENNReal.ofReal (generalLiouvillePhysicalDensity R s scale r)) r :=
      (generalLiouville_lintegral_change hR hd _).symm
    _ = generalLiouvillePhysicalMeasure R s scale t := by
      rw [lintegral_indicator ht, generalLiouvillePhysicalMeasure, withDensity_apply _ ht]

theorem generalLiouvillePullbackMeasure_eq (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s) (hpos : ∀ x, 0 < R x) :
    generalLiouvillePullbackMeasure R s scale =
      (generalLiouvilleModelMeasure R scale).withDensity (fun x => ENNReal.ofReal (s x ^ 2)) := by
  have hm : Measurable (fun x => ENNReal.ofReal (generalLiouvilleModelDensity R scale x)) :=
    (generalLiouvilleModelDensity_continuous hR hpos).measurable.ennreal_ofReal
  have hs2 : Measurable (fun x : ℝ => ENNReal.ofReal (s x ^ 2)) :=
    (hs.continuous.pow 2).measurable.ennreal_ofReal
  unfold generalLiouvillePullbackMeasure generalLiouvilleModelMeasure
  rw [← withDensity_mul volume hm hs2]
  congr 1
  funext x
  change ENNReal.ofReal (generalLiouvilleModelDensity R scale x * s x ^ 2) =
    ENNReal.ofReal (generalLiouvilleModelDensity R scale x) * ENNReal.ofReal (s x ^ 2)
  apply ENNReal.ofReal_mul
  unfold generalLiouvilleModelDensity
  positivity

private theorem positive_square_memLp_iff (μ : Measure ℝ) (s : ℝ → ℝ)
    (hs : Continuous s) (hpos : ∀ x, 0 < s x) (f : ℝ → ℝ) :
    MemLp f 2 (μ.withDensity (fun x => ENNReal.ofReal (s x ^ 2))) ↔
      MemLp (fun x => s x * f x) 2 μ := by
  have hd : Measurable (fun x : ℝ => ENNReal.ofReal (s x ^ 2)) :=
    (hs.pow 2).measurable.ennreal_ofReal
  have hac : μ ≪ μ.withDensity (fun x => ENNReal.ofReal (s x ^ 2)) := by
    apply withDensity_absolutelyContinuous' hd.aemeasurable
    exact Eventually.of_forall (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hpos x))))
  have hfinite : ∀ᵐ x ∂μ, ENNReal.ofReal (s x ^ 2) < (∞ : ℝ≥0∞) := by simp
  constructor
  · intro hf
    have hfm := AEStronglyMeasurable.mono_ac hac hf.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq (hs.aestronglyMeasurable.mul hfm)).mpr
    have h := (integrable_withDensity_iff_integrable_smul' hd hfinite).mp hf.integrable_sq
    convert h using 1
    funext x
    change (s x * f x) ^ 2 = (ENNReal.ofReal (s x ^ 2)).toReal • f x ^ 2
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    simp only [smul_eq_mul]
    ring
  · intro hf
    have hi : Continuous (fun x => (s x)⁻¹) := hs.inv₀ (fun x => (hpos x).ne')
    have hfm : AEStronglyMeasurable f μ := by
      have h := hi.aestronglyMeasurable.mul hf.aestronglyMeasurable
      convert h using 1
      funext x
      exact (inv_mul_cancel_left₀ (hpos x).ne' (f x)).symm
    have hfd := AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal (s x ^ 2))) hfm
    apply (memLp_two_iff_integrable_sq hfd).mpr
    apply (integrable_withDensity_iff_integrable_smul' hd hfinite).mpr
    convert hf.integrable_sq using 1
    funext x
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    simp only [smul_eq_mul]
    ring

theorem generalLiouville_memLp_iff (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) (u : ℝ → ℝ) :
    MemLp u 2 (generalLiouvillePhysicalMeasure R s scale) ↔
      MemLp (fun x => s x * u (R x)) 2 (generalLiouvilleModelMeasure R scale) := by
  have hd := fun x => (hp x).2.1
  have hpos := fun x => (hp x).1
  rw [← generalLiouville_map_measure hR hd hpos,
    (generalLiouville_measurableEmbedding hR hd).memLp_map_measure_iff,
    generalLiouvillePullbackMeasure_eq hscale hR hs hpos]
  exact positive_square_memLp_iff _ s hs.continuous (fun x => (hp x).2.2) _

theorem generalLiouville_spectral_integral (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) (g : ℝ → ℝ) :
    (∫ r, g r ∂generalLiouvillePhysicalMeasure R s scale) =
      ∫ x, s x ^ 2 * g (R x) ∂generalLiouvilleModelMeasure R scale := by
  have hs2 : Measurable (fun x : ℝ => ENNReal.ofReal (s x ^ 2)) :=
    (hs.continuous.pow 2).measurable.ennreal_ofReal
  rw [← generalLiouville_map_measure hR (fun x => (hp x).2.1) (fun x => (hp x).1),
    (generalLiouville_measurableEmbedding hR (fun x => (hp x).2.1)).integral_map,
    generalLiouvillePullbackMeasure_eq hscale hR hs (fun x => (hp x).1),
    integral_withDensity_eq_integral_toReal_smul hs2 (by simp)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem generalLiouville_pullback_ae (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) {f g : ℝ → ℝ}
    (hfg : f =ᵐ[generalLiouvillePhysicalMeasure R s scale] g) :
    (fun x => f (R x)) =ᵐ[generalLiouvilleModelMeasure R scale] (fun x => g (R x)) := by
  have hac : generalLiouvilleModelMeasure R scale ≪ generalLiouvillePullbackMeasure R s scale := by
    rw [generalLiouvillePullbackMeasure_eq hscale hR hs (fun x => (hp x).1)]
    apply withDensity_absolutelyContinuous' (hs.continuous.pow 2).measurable.ennreal_ofReal.aemeasurable
    exact Eventually.of_forall (fun x => ne_of_gt
      (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hp x).2.2)))
  apply hac.ae_eq
  have hmap := generalLiouville_map_measure (s := s) (scale := scale) hR
    (fun x => (hp x).2.1) (fun x => (hp x).1)
  exact ae_eq_comp hR.continuous.measurable.aemeasurable
    (by simpa only [hmap] using hfg)

theorem generalLiouville_pushforward_ae (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) {f g : ℝ → ℝ}
    (hfg : (fun x => f (R x)) =ᵐ[generalLiouvilleModelMeasure R scale]
      (fun x => g (R x))) : f =ᵐ[generalLiouvillePhysicalMeasure R s scale] g := by
  have hρ : (fun x => f (R x)) =ᵐ[generalLiouvillePullbackMeasure R s scale]
      (fun x => g (R x)) := by
    rw [generalLiouvillePullbackMeasure_eq hscale hR hs (fun x => (hp x).1)]
    exact (withDensity_absolutelyContinuous _ _).ae_eq hfg
  rw [← generalLiouville_map_measure hR (fun x => (hp x).2.1) (fun x => (hp x).1)]
  change (∀ᵐ r ∂Measure.map R (generalLiouvillePullbackMeasure R s scale), f r = g r)
  change (∀ᵐ x ∂generalLiouvillePullbackMeasure R s scale, f (R x) = g (R x)) at hρ
  simpa only [ae_iff, Set.preimage_ofPred_eq,
    (generalLiouville_measurableEmbedding hR (fun x => (hp x).2.1)).map_apply] using hρ

private theorem generalL2_norm_sq {μ : Measure ℝ} (u : Lp ℝ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem generalToLp_norm_sq {μ : Measure ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [generalL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

def generalLiouvillePullback (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) :
    GeneralLiouvillePhysicalL2 R s scale →ₗᵢ[ℝ] GeneralLiouvilleModelL2 R scale where
  toFun u := ((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u)).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards
      [((generalLiouville_memLp_iff hscale hR hs hp
          ((u + v : GeneralLiouvillePhysicalL2 R s scale) : ℝ → ℝ)).mp (Lp.memLp (u + v))).coeFn_toLp,
        ((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u)).coeFn_toLp,
        ((generalLiouville_memLp_iff hscale hR hs hp v).mp (Lp.memLp v)).coeFn_toLp,
        Lp.coeFn_add
          (((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u)).toLp _)
          (((generalLiouville_memLp_iff hscale hR hs hp v).mp (Lp.memLp v)).toLp _),
        generalLiouville_pullback_ae hscale hR hs hp (Lp.coeFn_add u v)] with x hx hu hv hadd ha
    simp only [Pi.add_apply] at hadd ha
    rw [hx, hadd, hu, hv, ha]
    ring
  map_smul' a u := by
    apply Lp.ext
    filter_upwards
      [((generalLiouville_memLp_iff hscale hR hs hp
          ((a • u : GeneralLiouvillePhysicalL2 R s scale) : ℝ → ℝ)).mp (Lp.memLp (a • u))).coeFn_toLp,
        ((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u)).coeFn_toLp,
        Lp.coeFn_smul a (((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u)).toLp _),
        generalLiouville_pullback_ae hscale hR hs hp (Lp.coeFn_smul a u)] with x hx hu hsmul ha
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul ha
    simp only [RingHom.id_apply]
    rw [hx, hsmul, hu, ha]
    ring
  norm_map' u := by
    change ‖((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u)).toLp _‖ = ‖u‖
    have ht := generalToLp_norm_sq ((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u))
    have hu := generalL2_norm_sq u
    rw [generalLiouville_spectral_integral hscale hR hs hp] at hu
    have heq : (fun x => (s x * u (R x)) ^ 2) = (fun x => s x ^ 2 * u (R x) ^ 2) := by
      funext x
      ring
    rw [heq] at ht
    nlinarith [norm_nonneg u,
      norm_nonneg (((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u)).toLp _)]

theorem generalLiouvillePullback_ae (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
    (u : GeneralLiouvillePhysicalL2 R s scale) :
    generalLiouvillePullback hscale hR hs hp u =ᵐ[generalLiouvilleModelMeasure R scale]
      (fun x => s x * u (R x)) :=
  ((generalLiouville_memLp_iff hscale hR hs hp u).mp (Lp.memLp u)).coeFn_toLp

theorem generalLiouvillePullback_surjective (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) :
    Function.Surjective (generalLiouvillePullback hscale hR hs hp) := by
  intro f
  let hm := (Lp.memLp f).aestronglyMeasurable
  let f0 := hm.mk f
  have hf0 : MemLp f0 2 (generalLiouvilleModelMeasure R scale) :=
    MemLp.ae_eq hm.ae_eq_mk (Lp.memLp f)
  let u : ℝ → ℝ := fun r => f0 (generalLiouvilleCoordinate R r) /
    s (generalLiouvilleCoordinate R r)
  have hu : MemLp u 2 (generalLiouvillePhysicalMeasure R s scale) := by
    rw [generalLiouville_memLp_iff hscale hR hs hp]
    convert hf0 using 1
    funext x
    dsimp only [u]
    rw [generalLiouvilleCoordinate_apply (fun x => (hp x).2.1)]
    field_simp [(hp x).2.2.ne']
  refine ⟨hu.toLp u, ?_⟩
  apply Lp.ext
  filter_upwards [generalLiouvillePullback_ae hscale hR hs hp (hu.toLp u),
    generalLiouville_pullback_ae hscale hR hs hp hu.coeFn_toLp, hm.ae_eq_mk] with x hx hu hf
  rw [hx, hu]
  dsimp only [u]
  rw [generalLiouvilleCoordinate_apply (fun x => (hp x).2.1)]
  change f x = f0 x at hf
  rw [← hf]
  field_simp [(hp x).2.2.ne']

def generalLiouvilleTransport (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) :
    GeneralLiouvilleModelL2 R scale ≃ₗᵢ[ℝ] GeneralLiouvillePhysicalL2 R s scale :=
  (LinearIsometryEquiv.ofSurjective (generalLiouvillePullback hscale hR hs hp)
    (generalLiouvillePullback_surjective hscale hR hs hp)).symm

theorem generalLiouvilleTransport_symm_ae (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
    (u : GeneralLiouvillePhysicalL2 R s scale) :
    (generalLiouvilleTransport hscale hR hs hp).symm u =ᵐ[generalLiouvilleModelMeasure R scale]
      (fun x => s x * u (R x)) :=
  generalLiouvillePullback_ae hscale hR hs hp u

theorem generalLiouvilleTransport_ae (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
    (ψ : GeneralLiouvilleModelL2 R scale) :
    generalLiouvilleTransport hscale hR hs hp ψ =ᵐ[generalLiouvillePhysicalMeasure R s scale]
      (fun r => ψ (generalLiouvilleCoordinate R r) / s (generalLiouvilleCoordinate R r)) := by
  apply generalLiouville_pushforward_ae hscale hR hs hp
  have h := generalLiouvilleTransport_symm_ae hscale hR hs hp
    (generalLiouvilleTransport hscale hR hs hp ψ)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  filter_upwards [h] with x hx
  rw [generalLiouvilleCoordinate_apply (fun x => (hp x).2.1)]
  apply (eq_div_iff (hp x).2.2.ne').mpr
  exact (mul_comm _ _).trans hx.symm

theorem generalLiouville_source_pairing
    (hR : ContDiff ℝ ∞ R) (hd : ∀ x, 0 < deriv R x) (u ψ f : ℝ → ℝ)
    (hu : ∀ x, u (R x) = ψ x / s x)
    (hint : IntegrableOn (fun r => u r * f r) (range R)) :
    Integrable (fun x => ψ x * (deriv R x / s x * f (R x))) ∧
      (∫ r in range R, u r * f r) = ∫ x, ψ x * (deriv R x / s x * f (R x)) := by
  have heq : (fun x => deriv R x * (u (R x) * f (R x))) =
      (fun x => ψ x * (deriv R x / s x * f (R x))) := by
    funext x
    rw [hu]
    ring
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact (generalLiouville_integrable_iff hR hd _).mp hint
  · rw [generalLiouville_integral_change hR hd, heq]

theorem generalLiouville_fullTransport (hscale : 0 < scale)
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) :
    Statements.LiouvilleFullTransport R s (generalLiouvilleProfile R s scale)
      (generalLiouvilleCoordinate R) scale := by
  refine ⟨⟨generalLiouvilleTransport hscale hR hs hp, ?_, ?_⟩, ?_⟩
  · exact generalLiouvilleTransport_ae hscale hR hs hp
  · exact generalLiouvilleTransport_symm_ae hscale hR hs hp
  · exact fun u ψ f hu hint => generalLiouville_source_pairing hR (fun x => (hp x).2.1) u ψ f hu hint

/-- The original unrestricted R02 target, on the actual range of each input radius. -/
theorem generalLiouville_R02_statement : Statements.R02Statement := by
  intro R s scale hscale hR hs hp
  have hd := fun x => (hp x).2.1
  refine ⟨generalLiouvilleCoordinate R, generalLiouvilleProfile R s scale,
    generalLiouvillePrimitive R s scale, generalLiouvilleCoordinate_apply hd,
    (fun _ hr => generalLiouvilleCoordinate_right hr), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    generalLiouville_fullTransport hscale hR hs hp⟩
  · rintro r ⟨x, rfl⟩
    exact (generalLiouvilleCoordinate_contDiffAt hR hd x).contDiffWithinAt
  · rintro r ⟨x, rfl⟩
    exact (generalLiouvilleProfile_contDiffAt hR hs hd x).contDiffWithinAt
  · rintro r ⟨x, rfl⟩
    exact (generalLiouvillePrimitive_contDiffAt hR hs hd x).contDiffWithinAt
  · intro x
    refine ⟨generalLiouvilleProfile_apply hd x, ?_⟩
    rw [generalLiouvilleProfile_apply hd]
    exact mul_pos (mul_pos hscale (sq_pos_of_pos (hp x).2.2)) (hd x)
  · rintro r ⟨x, rfl⟩
    exact generalLiouvillePrimitive_hasDerivAt hR hs hd x
  · intro ψ u hψ hu he j x
    exact generalLiouville_radialJacobi hR hs hp hψ hu he j x
  · intro x
    simpa only [generalLiouvillePhysicalDensity, generalLiouvillePullbackDensity,
      generalLiouvilleModelDensity, mul_comm] using
      generalLiouville_density (s := s) (scale := scale) hd (fun x => (hp x).1) x

end ContinuousFlexibility.Radial
