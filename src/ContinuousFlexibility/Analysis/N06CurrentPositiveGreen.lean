module

public import ContinuousFlexibility.Analysis.N06CurrentWeightedTraceGreen
public import ContinuousFlexibility.Analysis.N06WeakCylinderPDE

/-!
# Positive reference Green against actual current physical tests

The radial coefficient remains inside the flux, the angular coefficient
is radial, and the potential cancels in the symmetric pairing. Combining
the closed AC radial formula with the genuine periodic angular formula
gives the positive sign and both actual boundary terms. No smoothness of
the totalized inverse at the endpoints is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem integral_neg_sub_add {μ : Measure PolarPoint} {f g h : PolarPoint → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ p, -f p - g p + h p ∂μ) = -(∫ p, f p ∂μ) - (∫ p, g p ∂μ) + ∫ p, h p ∂μ := by
  have hneg : Integrable (fun p => -f p) μ := hf.neg
  have hsub : Integrable (fun p => -f p - g p) μ := hneg.sub hg
  rw [integral_add hsub hh, integral_sub hneg hg, integral_neg]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The positive radial-coefficient test operator is L2 on each actual
piece, by the true forward-chart test jet bounds. -/
theorem n06_currentHeight_positiveOperator_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {a c V : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V) :
    MemLp (n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ))
      2 (canonicalMeasure S K m) := by
  have hflux := n06_currentHeight_weighted_radial_memLp h04 hz hs hφ ha (m := m)
  have hθθ := (n06_current_canonicalHeight_second_memLp h04 hz hs m hφ).2
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  exact (hflux.neg.sub (n06_canonical_radialWeight_mul_memLp hc hθθ)).add
    (n06_canonical_radialWeight_mul_memLp hV hW)

/-- One actual C1/AC radial mode satisfies the full positive Green
identity against a current physical test. The potential cancels exactly. -/
theorem N06CurrentHeightTestTraces.tensor_positive_green
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi))
    {a c V v e : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hc : Continuous c) (hV : Continuous V) (hC : ContDiff ℝ 1 v)
    (hAC : AbsolutelyContinuousOnInterval (deriv v) (K.left m) (K.right m))
    (hv : MemLp v 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hflux : MemLp (deriv (fun y => a y * deriv v y)) 2
      (volume.restrict (Ioo (K.left m) (K.right m))))
    (he : ContDiff ℝ ∞ e) (hep : Function.Periodic e Real.pi) :
    (∫ p, (-deriv (fun y => a y * deriv v y) p.1 * e p.2 -
        (c p.1 * v p.1) * iteratedDeriv 2 e p.2 + (V p.1 * v p.1) * e p.2) *
          canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, (v p.1 * e p.2) *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi, e θ *
        (a (K.left m) * (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ)) -
        a (K.right m) * (P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ))) := by
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hfluxW := n06_currentHeight_weighted_radial_memLp h04 hz hs hφ ha (m := m)
  have hθθ := (n06_current_canonicalHeight_second_memLp h04 hz hs m hφ).2
  have hcv := n06_interval_memLp_mul_continuous hv hc
  have hVv := n06_interval_memLp_mul_continuous hv hV
  have hA : Integrable (fun p : PolarPoint =>
      (deriv (fun y => a y * deriv v y) p.1 * e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hflux he.continuous).integrable_mul hW
  have hB : Integrable (fun p : PolarPoint =>
      ((c p.1 * v p.1) * iteratedDeriv 2 e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hcv
        (circleFourier_contDiff_iteratedDeriv he 2).continuous).integrable_mul hW
  have hZ : Integrable (fun p : PolarPoint =>
      ((V p.1 * v p.1) * e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hVv he.continuous).integrable_mul hW
  have hR : Integrable (fun p : PolarPoint => (v p.1 * e p.2) *
      radialPartial (fun q => a q.1 * radialPartial (canonicalHeight S K z m φ) q) p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hv he.continuous).integrable_mul hfluxW
  have hT : Integrable (fun p : PolarPoint => ((c p.1 * v p.1) * e p.2) *
      angularPartial (angularPartial (canonicalHeight S K z m φ)) p)
      (canonicalMeasure S K m) :=
    (n06_canonical_tensor_memLp hcv he.continuous).integrable_mul hθθ
  have hleft :
      (∫ p, (-deriv (fun y => a y * deriv v y) p.1 * e p.2 -
          (c p.1 * v p.1) * iteratedDeriv 2 e p.2 + (V p.1 * v p.1) * e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
      -(∫ p, (deriv (fun y => a y * deriv v y) p.1 * e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, ((c p.1 * v p.1) * iteratedDeriv 2 e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) +
      ∫ p, ((V p.1 * v p.1) * e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m := by
    rw [← integral_neg_sub_add hA hB hZ]
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hright :
      (∫ p, (v p.1 * e p.2) *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
          ∂canonicalMeasure S K m) =
      -(∫ p, (v p.1 * e p.2) * radialPartial (fun q => a q.1 *
        radialPartial (canonicalHeight S K z m φ) q) p ∂canonicalMeasure S K m) -
      (∫ p, ((c p.1 * v p.1) * e p.2) *
        angularPartial (angularPartial (canonicalHeight S K z m φ)) p
          ∂canonicalMeasure S K m) +
      ∫ p, ((V p.1 * v p.1) * e p.2) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m := by
    rw [← integral_neg_sub_add hR hT hZ]
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [n06UnitReferenceTestOperator]
    ring
  have hr := P.tensor_weighted_radial_green h04 hz hs hφ ha hC hAC hv hflux he.continuous
  have ht := n06_currentHeight_tensor_angular_green h04 hz hs hφ hφp hcv he hep
  have hsign : (∫ θ in (0 : ℝ)..Real.pi, e θ *
        (a (K.left m) * (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ)) -
        a (K.right m) * (P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ)))) =
      -(∫ θ in (0 : ℝ)..Real.pi, e θ *
        (a (K.right m) * (P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ)) -
        a (K.left m) * (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ)))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [hleft, hright, hsign]
  linarith only [hr, ht]

end ContinuousFlexibility.Statements
