import ContinuousFlexibility.Analysis.N06NegativeFiniteCoreGreen
import ContinuousFlexibility.Analysis.N06ActualNegativeSourceIdentity

/-!
# The negative finite Green formula on the original atlas

Use the actual zero principal source on negative pieces. The original N05
weak equation still identifies the complete forcing, with all three scalar
columns. Every interval and both boundary terms remain unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

theorem n06N05_primitive_negative_finite_relative_green
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false)
    {G₀ : CanonicalL2 S K m} (P : N06NegativeGraphApproximation (u.val.1.1 m) G₀)
    (hG₀ : (G₀ : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06NegativePrincipalForcing D S C K u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m)
    (s : Finset ℕ)
    (hvalue : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s P.modes referenceAngularBasis)
    (G Fcur : CanonicalSequence S K)
    (hsource : (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G m)
    (hG : G m = 0)
    (hφ : RadialTest D φ)
    (Q : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ)) :
    (∫ p, n06CurrentRemainderSource D S C L K z u.val.1 Fcur m p *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (Q.value (K.right m, θ) *
            radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.right m, θ) -
          r11bFiniteSynthesis s P.modes referenceAngularBasis (K.right m, θ) *
            Q.radial (K.right m, θ)) -
        (Q.value (K.left m, θ) *
            radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.left m, θ) -
          r11bFiniteSynthesis s P.modes referenceAngularBasis (K.left m, θ) *
            Q.radial (K.left m, θ)) := by
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hforcing := n06N05_negative_finite_principalForcing hT hS h u m hm P hG₀ s hvalue
  have hrem := n06_currentRelativeSource_negative_remainder_ae_of_eq_zero u.val.1
    (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G Fcur m hm hsource hG
  have hleft :
      (∫ p, n06CurrentRemainderSource D S C L K z u.val.1 Fcur m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) =
      ∫ p, (n06FiniteMixedField s P.modes 2 0 p -
        p.1 * n06FiniteMixedField s P.modes 0 2 p +
        K.potential z m p * r11bFiniteSynthesis s P.modes referenceAngularBasis p) *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [hrem, hforcing, hvalue] with p hp hf hv
    rw [hp, hf, hv]
  rw [hleft]
  exact P.current_finset_fullPeriod_green Q hT hS h03 h04 hz hs hm hφ s

end ContinuousFlexibility.Analysis
