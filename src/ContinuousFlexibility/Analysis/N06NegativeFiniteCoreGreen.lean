import ContinuousFlexibility.Analysis.N06NegativeFiniteIdentification
import ContinuousFlexibility.Analysis.N06NegativeFullPeriodGreen
import ContinuousFlexibility.Analysis.N06CurrentRelativeSourceIdentity
import ContinuousFlexibility.Analysis.N06CutTransmissionJets

/-!
# The actual negative finite core and its current Green source

The original N05 weak equation identifies the principal forcing of a
finite height with the principal expression of its actual H2 modes.
The literal relative source then gives the current remainder, including
all three current-minus-reference columns. Its cubic contribution on a
negative piece vanishes by the original compact-test characterization.

The resulting Green formula applies to an arbitrary common finite set
of modes and every original full-period physical test. No finite support
of the raw source, added weak equation, or endpoint inverse is assumed.
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

/-- The true full-period negative Green identity works with the common
finite set of the original graph core, not only an initial truncation. -/
theorem N06NegativeGraphApproximation.current_finset_fullPeriod_green
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    (Q : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ))
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : RadialTest D φ) (s : Finset ℕ) :
    (∫ p, (n06FiniteMixedField s P.modes 2 0 p -
        p.1 * n06FiniteMixedField s P.modes 0 2 p +
        K.potential z m p * r11bFiniteSynthesis s P.modes referenceAngularBasis p) *
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
  have hW : MemLp (r11bFiniteSynthesis s P.modes referenceAngularBasis)
      2 (canonicalMeasure S K m) := by
    unfold r11bFiniteSynthesis
    exact memLp_finsetSum s (fun i _ => n06_canonical_tensor_memLp
      (P.mode_memLp i) (contDiff_referenceAngularBasis i).continuous)
  have havg :
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p
          ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [n06_negative_current_source_average hT hS h03 h04 hz hs hm hφ
      ⟨hp.1, mem_univ _⟩]
  rw [havg, n06_negative_current_pairing_rewrite h04 hz hs hm
    (n06_radialTestAverage_test hφ).1 hW (P.finite_principal_memLp s)]
  have hderiv : radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) =
      n06FiniteMixedField s P.modes 1 0 := by
    simpa only [n06FiniteMixedField, iteratedDeriv_one, iteratedDeriv_zero] using
      n06_radialPartial_finiteSynthesis_one s P.modes referenceAngularBasis
        (fun i _ => P.contDiff i)
        (fun i _ => (contDiff_referenceAngularBasis i).of_le (by simp))
  rw [hderiv]
  exact Q.finite_negative_green h04 hz hs (n06_radialTestAverage_test hφ).1
    (n06_radialTestAverage_periodic hφ.2.1) s P.modes
    (fun i _ => P.contDiff i) (fun i _ => P.deriv_ac i)
    (fun i _ => P.mode_memLp i) (fun i _ => P.second_memLp i)

/-- The principal forcing is identified from the original N05 graph
itself. In particular the compatibility column is not truncated away. -/
theorem n06N05_negative_finite_principalForcing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false)
    {G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation (u.val.1.1 m) G)
    (hG : (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06NegativePrincipalForcing D S C K u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m)
    (s : Finset ℕ)
    (hvalue : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s P.modes referenceAngularBasis) :
    n06NegativePrincipalForcing D S C K u.val.1
      (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m =ᵐ[canonicalMeasure S K m]
      fun p => n06FiniteMixedField s P.modes 2 0 p -
        p.1 * n06FiniteMixedField s P.modes 0 2 p := by
  have hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, u.val.1.1 m p * n06NegativePrincipalTest ψ p ∂canonicalMeasure S K m) =
        ∫ p, G p * ψ p ∂canonicalMeasure S K m := by
    intro ψ hψ
    refine (n06N05_negative_principal_pairing hT hS h u m hm hψ).trans ?_
    apply integral_congr_ae
    filter_upwards [hG] with p hp
    rw [hp]
  exact hG.symm.trans (P.forcing_eq_finitePrincipal_of_height D s hvalue hweak)

/-- The actual relative source satisfies the finite negative Green
formula. Its only source inputs are its literal field formula and the
defining cubic pairing, both supplied by the constructed source maps. -/
theorem n06N05_negative_finite_relative_green
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
    {A Bc Cc : ℕ → PolarPoint → ℝ}
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, G m p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u.val.1.1 m p * n06PositiveCubicTestOperator K A Bc Cc m ψ p
          ∂canonicalMeasure S K m)
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
  have hrem := n06_currentRelativeSource_negative_remainder_ae u.val.1
    (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G Fcur m hm hsource hweak
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
