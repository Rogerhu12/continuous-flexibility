import ContinuousFlexibility.Analysis.N06PrimitiveFiniteForcing
import ContinuousFlexibility.Analysis.N06PrimitiveCubicTestLp
import ContinuousFlexibility.Analysis.N06PositiveFullPeriodTests
import ContinuousFlexibility.Analysis.N06CurrentRelativeSourceIdentity

/-!
# Actual positive finite Green on the original canonical interval

The complete original forcing is identified by compact tests.  The actual
interval cubic pairing applies to the half-period average of every original
physical test.  Only the same finite H2 height and its true weighted
endpoint Wronskians remain; no unit geometry or smooth forcing is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {a c pot : ℝ → ℝ} {φ : PolarPoint → ℝ}

/-- The actual source algebra on an arbitrary positive interval leaves
exactly the reference Green expression.  The cubic equation is extended
from compact tests by its true two-endpoint vanishing factor. -/
theorem n06_primitive_positive_relative_pairing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true)
    (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hpot : Continuous pot)
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun q => a q.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun q => c q.1) (canonicalOpen S K m))
    (hepot : EqOn (K.potential (C.referenceState, 0) m)
      (fun q => pot q.1) (canonicalOpen S K m))
    (U g : CanonicalL2 S K m) {F : PolarPoint → ℝ}
    (hF : MemLp F 2 (canonicalMeasure S K m))
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, U p * divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
            (K.dividedDifference z m).a (K.dividedDifference z m).b
            (K.dividedDifference z m).c) ψ p ∂canonicalMeasure S K m)
    (hφ : RadialTest D φ) :
    (∫ p, (-F p + g p -
        (K.potential z m p - K.potential (C.referenceState, 0) m p) * U p) *
          canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, U p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      (∫ p, U p * n06UnitReferenceTestOperator a c pot
        (canonicalHeight S K z m (n06_radialTestAverage φ)) p ∂canonicalMeasure S K m) -
        ∫ p, F p * canonicalHeight S K z m (n06_radialTestAverage φ) p
          ∂canonicalMeasure S K m := by
  let W := canonicalHeight S K z m (n06_radialTestAverage φ)
  let A := n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
    (K.dividedDifference z m).a (K.dividedDifference z m).b (K.dividedDifference z m).c
  let ΔV : PolarPoint → ℝ := fun p => K.potential z m p - K.potential (C.referenceState, 0) m p
  let Lφ := canonicalSource S K z m
    (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ))
  have hψ := n06_radialTestAverage_test hφ
  have hW : MemLp W 2 (canonicalMeasure S K m) :=
    n06_current_canonicalHeight_memLp h04 hz hs m hψ.1.continuous.continuousOn
  have hPW := n06_currentHeight_positiveOperator_memLp_C1 h04 hz hs hψ.1 ha hc hpot
    (m := m)
  have hDW : MemLp (divergenceOperator A W) 2 (canonicalMeasure S K m) :=
    n06_primitive_cubicTest_memLp hT hS h01 h03 h04 href hcur hz hs hm
      ha hc hpot hcd hea heb hec hepot hψ
  have hDU : MemLp (fun p => ΔV p * U p) 2 (canonicalMeasure S K m) :=
    n06_positive_potentialDifference_mul_memLp h04 hz hs hpot hepot (Lp.memLp U)
  have hDW₀ : MemLp (fun p => ΔV p * W p) 2 (canonicalMeasure S K m) :=
    n06_positive_potentialDifference_mul_memLp h04 hz hs hpot hepot hW
  have hEq : Lφ =ᵐ[canonicalMeasure S K m] fun p =>
      -n06UnitReferenceTestOperator a c pot W p + divergenceOperator A W p - ΔV p * W p := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    change canonicalSource S K z m
      (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p = _
    rw [n06_positive_current_source_average hT hS h01 h03 h04 hz hs m hm hφ.1 hpU]
    exact n06_primitive_positive_operatorTest_difference h01 h04 href hcur hz hs hm
      ha hea heb hec hepot hψ.1 hpU (hcd p.1 hp.1)
  have hLW : MemLp Lφ 2 (canonicalMeasure S K m) :=
    (memLp_congr_ae hEq).mpr ((hPW.neg.add hDW).sub hDW₀)
  have hsource : MemLp (fun p => -F p + g p - ΔV p * U p)
      2 (canonicalMeasure S K m) := (hF.neg.add (Lp.memLp g)).sub hDU
  have hI : Integrable (fun p => (-F p + g p - ΔV p * U p) * W p)
      (canonicalMeasure S K m) := hsource.integrable_mul hW
  have hJ : Integrable (fun p => U p * Lφ p) (canonicalMeasure S K m) :=
    (Lp.memLp U).integrable_mul hLW
  have hUP : Integrable (fun p => U p * n06UnitReferenceTestOperator a c pot W p)
      (canonicalMeasure S K m) := (Lp.memLp U).integrable_mul hPW
  have hFW : Integrable (fun p => F p * W p) (canonicalMeasure S K m) := hF.integrable_mul hW
  have hgW : Integrable (fun p => g p * W p) (canonicalMeasure S K m) :=
    (Lp.memLp g).integrable_mul hW
  have hUC : Integrable (fun p => U p * divergenceOperator A W p)
      (canonicalMeasure S K m) := (Lp.memLp U).integrable_mul hDW
  have hcubic : (∫ p, g p * W p ∂canonicalMeasure S K m) =
      ∫ p, U p * divergenceOperator A W p ∂canonicalMeasure S K m :=
    n06_primitive_cubic_pairing_fullPhysical_test hT hS h01 h03 h04 href hcur hz hs hm
      ha hc hpot hcd hea heb hec hepot U g hweak hφ
  calc
    _ = ∫ p, ((U p * n06UnitReferenceTestOperator a c pot W p - F p * W p) +
        (g p * W p - U p * divergenceOperator A W p)) ∂canonicalMeasure S K m := by
      rw [← integral_sub hI hJ]
      apply integral_congr_ae
      filter_upwards [hEq] with p hp
      rw [hp]
      ring
    _ = ((∫ p, U p * n06UnitReferenceTestOperator a c pot W p ∂canonicalMeasure S K m) -
        ∫ p, F p * W p ∂canonicalMeasure S K m) +
        ((∫ p, g p * W p ∂canonicalMeasure S K m) -
          ∫ p, U p * divergenceOperator A W p ∂canonicalMeasure S K m) := by
      have hleft : Integrable (fun p => U p * n06UnitReferenceTestOperator a c pot W p -
          F p * W p) (canonicalMeasure S K m) := hUP.sub hFW
      have hright : Integrable (fun p => g p * W p - U p * divergenceOperator A W p)
          (canonicalMeasure S K m) := hgW.sub hUC
      rw [integral_add hleft hright, integral_sub hUP hFW, integral_sub hgW hUC]
    _ = _ := by rw [hcubic, sub_self, add_zero]

variable {Vol : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K Vol b}

/-- The same finite original height and source give the full current
Green identity, with its two true weighted endpoint terms. -/
theorem n06N05_primitive_positive_finite_relative_green
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (hm : K.positive m = true)
    (ha : ContDiff ℝ 1 a) (hc : Continuous c) (hpot : Continuous pot)
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun q => a q.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun q => c q.1) (canonicalOpen S K m))
    (hepot : EqOn (K.potential (C.referenceState, 0) m)
      (fun q => pot q.1) (canonicalOpen S K m))
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m))
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hvalue : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s v referenceAngularBasis)
    (G Fcur : CanonicalSequence S K)
    (hsource : (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, G m p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u.val.1.1 m p * divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
            (K.dividedDifference z m).a (K.dividedDifference z m).b
            (K.dividedDifference z m).c) ψ p ∂canonicalMeasure S K m)
    (hφ : RadialTest D φ)
    (Q : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ)) :
    (∫ p, n06CurrentRemainderSource D S C L K z u.val.1 Fcur m p *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a (K.right m) * (Q.value (K.right m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.right m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * Q.radial (K.right m, θ)) -
        a (K.left m) * (Q.value (K.left m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.left m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * Q.radial (K.left m, θ)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hforcing := n06N05_primitive_positive_finite_referenceForcing hT hS h u hm
    ha hc hpot hcd hea heb hec hepot s v hC hAC hv hv₁ hv₂ hvalue
  have hrem := n06_currentRelativeSource_positive_remainder_ae u.val.1
    (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G Fcur m hm hsource
  have hpair := n06_primitive_positive_relative_pairing hT hS h01 h03 h04 href hcur
    hz hs hm ha hc hpot hcd hea heb hec hepot (u.val.1.1 m) (G m)
    (n06N05_primitive_referenceForcing_memLp hT hS h u m) hweak hφ
  have hleft :
      (∫ p, n06CurrentRemainderSource D S C L K z u.val.1 Fcur m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) =
      ∫ p, (-n06ReferenceCanonicalForcing D S C K u.val.1
          (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m p + G m p -
        (K.potential z m p - K.potential (C.referenceState, 0) m p) * u.val.1.1 m p) *
          canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [hrem] with p hp
    rw [hp]
  have hheight (g : PolarPoint → ℝ) :
      (∫ p, u.val.1.1 m p * g p ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s v referenceAngularBasis p * g p
        ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [hvalue] with p hp
    rw [hp]
  have hforce :
      (∫ p, n06ReferenceCanonicalForcing D S C K u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m p *
          canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s (n06PrimitiveModalForcing a c pot v) referenceAngularBasis p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [hforcing] with p hp
    rw [hp]
  have hf (i : ℕ) (hi : i ∈ s) := n06_primitiveModalForcing_memLp
    (h04.1.referenceBounds m).2.1.le i ha hc hpot (hAC i hi) (hv i hi) (hv₁ i hi) (hv₂ i hi)
  have hg := Q.finite_positive_green_C1 h04 hz hs (n06_radialTestAverage_test hφ).1
    (n06_radialTestAverage_periodic hφ.2.1) ha hc hpot s v
    (n06PrimitiveModalForcing a c pot v) hC hAC hv hf
    (fun _ _ => Eventually.of_forall fun _ => rfl)
  have hsign : (∫ θ in (0 : ℝ)..Real.pi,
      a (K.right m) * (Q.value (K.right m, θ) *
        radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.right m, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * Q.radial (K.right m, θ)) -
      a (K.left m) * (Q.value (K.left m, θ) *
        radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.left m, θ) -
          r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * Q.radial (K.left m, θ))) =
      -(∫ θ in (0 : ℝ)..Real.pi,
        a (K.left m) * (Q.value (K.left m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.left m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.left m, θ) * Q.radial (K.left m, θ)) -
        a (K.right m) * (Q.value (K.right m, θ) *
          radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (K.right m, θ) -
            r11bFiniteSynthesis s v referenceAngularBasis (K.right m, θ) * Q.radial (K.right m, θ))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [hheight, hheight, hforce] at hpair
  rw [hleft, hsign]
  linarith only [hpair, hg]

end ContinuousFlexibility.Analysis
