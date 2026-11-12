import ContinuousFlexibility.Analysis.RadialGaugePrincipalFiniteJets
import ContinuousFlexibility.Analysis.WholePositivePrincipalExtension
import ContinuousFlexibility.Analysis.PositiveChartRangeGeometry

/-!
# Smooth representatives after the same fixed radial gauge

The physical representative is pulled back through the actual reference
inverse and multiplied by the exact principal multiplier. Its germs
therefore equal the displayed current-minus-reference principal field
on the entire closed canonical cylinder. The charts and height remain
the original chosen functions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem exists_referenceGaugePrincipal_difference_extension
    {A A₀ : SymmetricCoefficients}
    {τ σ τ₀ σ₀ : PolarPoint → PolarPoint} {Q Q₀ : PolarPoint → ℝ}
    {Y H₀ : ℝ → ℝ} {a l r b c d c₀ d₀ : ℝ}
    (hal : a < l) (hlr : l < r) (hrb : r < b)
    (hgeometry : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    (hgeometry₀ : WholePositiveChartGeometry σ₀ τ₀
      (wholePositiveChartHeight σ₀ Q₀) l r c₀ d₀)
    (hτ₀ : τ₀ = id) (hσ₀ : σ₀ = id) (hQ₀ : Q₀ = (fun _ => 1))
    (hG : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H₀ p.1) l r 0 1)
    (ha : ContDiffOn ℝ ∞ A.a (Ioo a b ×ˢ (univ : Set ℝ)))
    (hb : ContDiffOn ℝ ∞ A.b (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc : ContDiffOn ℝ ∞ A.c (Ioo a b ×ˢ (univ : Set ℝ)))
    (ha₀ : ContDiffOn ℝ ∞ A₀.a (Ioo a b ×ˢ (univ : Set ℝ)))
    (hb₀ : ContDiffOn ℝ ∞ A₀.b (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc₀ : ContDiffOn ℝ ∞ A₀.c (Ioo a b ×ˢ (univ : Set ℝ))) :
    let B := inverseChartPrincipalCoefficients A
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ)
      (wholePositiveReferenceGaugeInverse τ (positiveReferenceCylinderInverse Y))
      (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H₀ p.1) σ Q)
    let B₀ := inverseChartPrincipalCoefficients A₀
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ₀)
      (wholePositiveReferenceGaugeInverse τ₀ (positiveReferenceCylinderInverse Y))
      (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H₀ p.1) σ₀ Q₀)
    ∃ F : Fin 3 → PolarPoint → ℝ, (∀ v, ContDiff ℝ ∞ (F v)) ∧
      ∀ v p, p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) →
        F v =ᶠ[𝓝 p] (fun q => canonicalCoefficientComponent v B q -
          canonicalCoefficientComponent v B₀ q) := by
  have hY : ContDiff ℝ ∞ Y := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def] using
      hG.chart_smooth.fst.comp (contDiff_id.prodMk (contDiff_const :
        ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))))
  have hH₀ : ContDiff ℝ ∞ H₀ := by
    simpa only [Function.comp_def] using
      hG.height_smooth.comp (contDiff_id.prodMk (contDiff_const :
        ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))))
  have hYpos (r : ℝ) : 0 < deriv Y r := by
    simpa only [planeJacobian_positiveReferenceCylinderChart
      (hY.differentiable (by simp) r)] using hG.jacobian_positive (r, 0)
  have href := (wholePositiveCanonicalFields_reference A₀ hτ₀ hσ₀ hQ₀).2.1
  obtain ⟨F, hF, he⟩ := exists_wholePositivePrincipal_difference_extension
    hal hlr hrb hgeometry ha hb hc ha₀ hb₀ hc₀
  refine ⟨fun v p => radialGaugePrincipalMultiplier Y H₀ v p *
    F v (positiveReferenceCylinderInverse Y p), ?_, ?_⟩
  · intro v
    exact (contDiff_radialGaugePrincipalMultiplier hY hH₀ hG.inverse_smooth hYpos v).mul
      ((hF v).comp hG.inverse_smooth)
  · intro v p hp
    have hg := (he v (positiveReferenceCylinderInverse Y p)
      (hG.inverse_maps_closed hp)).comp_tendsto
        (hG.inverse_smooth.continuous.tendsto p)
    filter_upwards [hg] with q hq
    have hcurrent := congrFun
      (wholePositiveReferenceGauge_principal_component A hgeometry hY hYpos v) q
    have hreference := congrFun
      (wholePositiveReferenceGauge_principal_component A₀ hgeometry₀ hY hYpos v) q
    rw [href] at hreference
    simp only [Function.comp_apply] at hq
    rw [hcurrent, hreference, hq]
    ring

end ContinuousFlexibility.Analysis
