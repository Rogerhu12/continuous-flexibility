import ContinuousFlexibility.Analysis.N06CurrentOperatorRegularity
import ContinuousFlexibility.Analysis.N06PositiveFullPeriodTests
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Conservation of the actual correction after the left cutoff

The cutoff derivative is supported where N03 preserves the original
coefficient germs. Elsewhere the cutoff is locally constant. Thus its
commutator with the difference of the two actual operators is zero,
without assuming smoothness of the corrected coefficients on negative
pieces. Applying N03's source conservation to the genuine compact test
`chiLeft * phi` gives the weighted conservation identity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

/-- Constant multiplication commutes with the totalized derivative over
the scalar field, including at a nondifferentiable point. -/
theorem n06_fderiv_const_mul_unconditional (f : PolarPoint → ℝ) (c : ℝ)
    (p v : PolarPoint) :
    fderiv ℝ (fun q => c * f q) p v = c * fderiv ℝ f p v := by
  change fderiv ℝ (c • f) p v = _
  rw [fderiv_const_smul_field]
  rfl

theorem n06_divergenceOperator_const_mul_unconditional
    (A : SymmetricCoefficients) (f : PolarPoint → ℝ) (c : ℝ) (p : PolarPoint) :
    divergenceOperator A (fun q => c * f q) p = c * divergenceOperator A f p := by
  have hr : radialPartial (fun q => c * f q) = fun q => c * radialPartial f q :=
    funext (fun q => n06_fderiv_const_mul_unconditional f c q (1, 0))
  have ht : angularPartial (fun q => c * f q) = fun q => c * angularPartial f q :=
    funext (fun q => n06_fderiv_const_mul_unconditional f c q (0, 1))
  have hN : (fun q => A.a q * (c * radialPartial f q) +
      A.b q * (c * angularPartial f q)) =
      fun q => c * (A.a q * radialPartial f q + A.b q * angularPartial f q) := by
    funext q
    ring
  have hT : (fun q => A.b q * (c * radialPartial f q) +
      A.c q * (c * angularPartial f q)) =
      fun q => c * (A.b q * radialPartial f q + A.c q * angularPartial f q) := by
    funext q
    ring
  unfold divergenceOperator
  rw [hr, ht, hN, hT]
  simp only [radialPartial, angularPartial, n06_fderiv_const_mul_unconditional]
  ring

/-- A smooth cutoff is genuinely constant near every point outside a
closed support for its derivative. -/
theorem n06_cutoff_locally_constant
    {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → deriv χ r = 0) {r : ℝ} (hr : r ∉ J) :
    χ =ᶠ[𝓝 r] (fun _ => χ r) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hJ.isOpen_compl.mem_nhds hr)
  filter_upwards [Metric.ball_mem_nhds r hδ] with s hs
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball r δ).isPreconnected
    hχ.differentiableOn (fun x hx => hzero x (hball hx)) hs (Metric.mem_ball_self hδ)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

/-- The exact commutator cancellation uses the actual physical cutoff
and the N03 positive germs. -/
theorem n06_cutoff_correction_commutes
    (hS : IsPhysicalSpaces D T S) (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (φ : PolarPoint → ℝ) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (originalCoefficients D S C z) (fun q => S.chiLeft q.1 * φ q) p -
        divergenceOperator (L.coefficients z) (fun q => S.chiLeft q.1 * φ q) p =
      S.chiLeft p.1 * (divergenceOperator (originalCoefficients D S C z) φ p -
        divergenceOperator (L.coefficients z) φ p) := by
  have hχ : CutoffConditions D S.chiLeft := hS.2.2.1
  obtain ⟨J, hJ, _, hpos, hzero⟩ := hχ.2.2
  by_cases hpJ : p.1 ∈ J
  · rw [n06_correctedDivergence_eq_original_of_nonneg h03 hz hs hp (hpos p.1 hpJ).le,
      n06_correctedDivergence_eq_original_of_nonneg h03 hz hs hp (hpos p.1 hpJ).le,
      sub_self, sub_self, mul_zero]
  · have hg : (fun q : PolarPoint => S.chiLeft q.1 * φ q) =ᶠ[𝓝 p]
        (fun q => S.chiLeft p.1 * φ q) := by
      filter_upwards [(n06_cutoff_locally_constant (hχ.1.differentiable (by simp))
        hJ.isClosed hzero hpJ).comp_tendsto (continuous_fst.tendsto p)] with q hq
      dsimp only [Function.comp_def] at hq
      rw [hq]
    rw [n05_divergenceOperator_congr _ hg, n05_divergenceOperator_congr _ hg,
      n06_divergenceOperator_const_mul_unconditional,
      n06_divergenceOperator_const_mul_unconditional]
    ring

/-- N03's actual source conservation applied to a realized compact
cutoff test. Neither a weighted error condition nor coefficient
regularity on negative pieces is an additional hypothesis. -/
theorem n06_cutoff_correction_conservation
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (heven : ∀ r θ, φ (r, -θ) = φ (r, θ))
    (hperiod : Function.Periodic φ (0, Real.pi))
    (hsupport : HasCompactRadialSupport D φ) :
    physicalSourceIntegral D (fun p => S.chiLeft p.1 *
      (divergenceOperator (originalCoefficients D S C z) φ p -
        divergenceOperator (L.coefficients z) φ p)) = 0 := by
  let f : PolarPoint → ℝ := fun p => S.chiLeft p.1 * φ p
  have hf : ContDiff ℝ ∞ f := (hS.2.2.1.1.comp contDiff_fst).mul hφ
  have he : ∀ r θ, f (r, -θ) = f (r, θ) := by
    intro r θ
    change S.chiLeft r * φ (r, -θ) = S.chiLeft r * φ (r, θ)
    rw [heven]
  have hp : Function.Periodic f (0, Real.pi) := by
    intro p
    simp only [f, Prod.fst_add, add_zero, hperiod p]
  have hc : HasCompactRadialSupport D f := by
    obtain ⟨J, hJ, hJD, hzero⟩ := hsupport
    refine ⟨J, hJ, hJD, fun r hr θ => ?_⟩
    simp only [f, hzero r hr θ, mul_zero]
  obtain ⟨η, hη⟩ := n05_exists_heightPair_of_compact_test hT hS hf he hp hc
  have hconserve := h03.2.2.2.2.2.2.1 z hz hs (R.residual z) η
  refine Eq.trans ?_ hconserve
  unfold physicalSourceIntegral
  apply intervalIntegral.integral_congr_Ioo_of_le h01.1.1.choose_spec.1.2.1.le
  intro r hr
  dsimp only
  apply congrArg angularMean
  funext θ
  have hpoint := h03.2.2.2.2.2.1 z hz hs η (r, θ) ⟨hr, mem_univ _⟩
  rw [hη] at hpoint
  exact (n06_cutoff_correction_commutes hS h03 hz hs φ
    (p := (r, θ)) ⟨hr, mem_univ _⟩).symm.trans hpoint

end ContinuousFlexibility.Statements
