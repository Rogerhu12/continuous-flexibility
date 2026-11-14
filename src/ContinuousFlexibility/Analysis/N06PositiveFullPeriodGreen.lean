module

public import ContinuousFlexibility.Analysis.N06CurrentPositiveRelativePairing
public import ContinuousFlexibility.Analysis.N06PositiveFullPeriodTests
public import ContinuousFlexibility.Analysis.N06N05CurrentCubicPairing

/-!
# Positive current Green for the original physical test class

The same positive cubic control supplies the finite coefficient bounds.
The test is the actual half-period average of an arbitrary original
RadialTest. The source on the operator side is the average of the true
physical operator, by the positive N03 germs, rather than an assumed
periodicity property of its bare coefficient fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Finite actual positive relative Green for every original physical
test. The same original cubic control and source are used throughout;
both true weighted endpoint Wronskians remain explicit for cancellation. -/
theorem N06UnitWeakGraphData.current_positive_fullPeriod_green
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {Kc : CanonicalData S}
    {base loss b m : ℕ} {ε κ : ℝ} {z : AnnularState S × ℝ}
    {a c V : ℝ → ℝ} {φ : PolarPoint → ℝ}
    {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)}
    (P : N06UnitWeakGraphData a c V U F κ)
    (Q : N06CurrentHeightTestTraces S Kc z m (n06_radialTestAverage φ))
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L Kc base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : Kc.positive m = true) (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V)
    (hcd : ∀ y ∈ Ioo (Kc.left m) (Kc.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (Kc.coefficients (C.referenceState, 0) m).a
      (fun q => a q.1) (canonicalOpen S Kc m))
    (heb : EqOn (Kc.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S Kc m))
    (hec : EqOn (Kc.coefficients (C.referenceState, 0) m).c
      (fun q => c q.1) (canonicalOpen S Kc m))
    (heV : EqOn (Kc.potential (C.referenceState, 0) m)
      (fun q => V q.1) (canonicalOpen S Kc m))
    {scale : ℕ → ℝ} {δ : ℝ}
    (hcoeff : N06PositiveCubicControl Kc b scale δ
      (fun n => (Kc.dividedDifference z n).a) (fun n => (Kc.dividedDifference z n).b)
      (fun n => (Kc.dividedDifference z n).c))
    (s : Finset ℕ) (g : CanonicalL2 S Kc m)
    (hweak : ∀ ψ, CanonicalTest S Kc m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S Kc m) =
        ∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) (Kc.dividedDifference z m).a
            (Kc.dividedDifference z m).b (Kc.dividedDifference z m).c) ψ p
              ∂canonicalMeasure S Kc m)
    (hφ : RadialTest D φ) :
    (∫ p, (-r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p +
        g p - (Kc.potential z m p - Kc.potential (C.referenceState, 0) m p) *
          r11bFiniteSynthesis s P.modes referenceAngularBasis p) *
            canonicalHeight S Kc z m (n06_radialTestAverage φ) p ∂canonicalMeasure S Kc m) -
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
        canonicalSource S Kc z m
          (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
            ∂canonicalMeasure S Kc m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a 1 * (Q.value (1, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (1, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (1, θ) * Q.radial (1, θ)) -
        a 0 * (Q.value (0, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (0, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (0, θ) * Q.radial (0, θ)) := by
  have hmid : ((1 / 2 : ℝ), (0 : ℝ)) ∈ canonicalOpen S Kc m := by
    simp only [canonicalOpen, hl, hr, mem_prod, mem_Ioo, mem_univ, and_true]
    norm_num
  have hδm : 0 ≤ δ * scale m :=
    (abs_nonneg ((Kc.dividedDifference z m).a ((1 / 2 : ℝ), 0))).trans
      (hcoeff.actual_firstJets m hm _ hmid).1
  have heq :
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
        canonicalSource S Kc z m
          (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
            ∂canonicalMeasure S Kc m) =
      ∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
        canonicalSource S Kc z m
          (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p
            ∂canonicalMeasure S Kc m := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [n06_positive_current_source_average hT hS h01 h03 h04 hz hs m hm hφ.1
      ⟨hp.1, mem_univ _⟩]
  rw [heq]
  exact P.current_positive_relative_finite_green Q h04 hz hs hm hl hr ha hc hV hcd
    hea heb hec heV hδm (hcoeff.a_smooth m hm) (hcoeff.b_smooth m hm)
    (hcoeff.c_smooth m hm) (hcoeff.actual_firstJets m hm) s g hweak
    (n06_radialTestAverage_test hφ).1 (n06_radialTestAverage_periodic hφ.2.1)

end ContinuousFlexibility.Analysis
