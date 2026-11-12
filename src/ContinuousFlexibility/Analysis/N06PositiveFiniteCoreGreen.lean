import ContinuousFlexibility.Analysis.N06PositiveFiniteForcing
import ContinuousFlexibility.Analysis.N06PositiveFullPeriodGreen
import ContinuousFlexibility.Analysis.N06ReferenceUnitEquation
import ContinuousFlexibility.Analysis.N06CurrentRelativeSourceIdentity

/-!
# The actual positive finite core and its current Green source

The compact weak equation is obtained from the same original N05 graph.
When its height is a finite synthesis of the actual modal representatives,
the original forcing is that same finite synthesis of its coefficients.
In particular the compatibility column is retained without assuming that
the unmodified source or that column has finite angular support.

The actual relative source then has precisely the positive Green sign:
minus reference forcing, plus cubic source, minus potential difference.
All three current-minus-reference scalar columns have already been
subtracted in the genuine current remainder.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b base loss m : ℕ} {ε κ : ℝ}
  {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}
  {a c pot : ℝ → ℝ} {φ : PolarPoint → ℝ}
  {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)}

/-- The actual source of the same original N05 graph is finite once its
actual height is finite. The weak PDE is derived, not added as a premise. -/
theorem n06N05_positive_finite_referenceForcing
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (u : B.Space) (hm : K.positive m = true)
    (P : N06UnitWeakGraphData a c pot U F κ)
    (hU : U 0 = u.val.1.1 m)
    (hF : (F 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06ReferenceCanonicalForcing D S C K u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m)
    (hl : K.left m = 0) (hr : K.right m = 1)
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hpot : Continuous pot)
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a p.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c p.1) (canonicalOpen S K m))
    (hepot : EqOn (K.potential (C.referenceState, 0) m)
      (fun p => pot p.1) (canonicalOpen S K m))
    (s : Finset ℕ)
    (hvalue : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s P.modes referenceAngularBasis) :
    n06ReferenceCanonicalForcing D S C K u.val.1
      (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  obtain ⟨hA, hB⟩ := n06_N04_qualitative_parts h04
  have hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, U 0 p * n06UnitReferenceTestOperator a c pot ψ p ∂canonicalMeasure S K m) =
        ∫ p, F 0 p * ψ p ∂canonicalMeasure S K m := by
    intro ψ hψ
    rw [hU]
    refine (n06N05_positive_unitWeakPairing h01.1.1 h01.1.2.2.2.1 hS h03 hA hB h.2
      h01.2.2.1 href hsector u hm hea heb hec hepot hcd hψ).trans ?_
    apply integral_congr_ae
    filter_upwards [hF] with p hp
    rw [hp]
  have hvalueU : (U 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s P.modes referenceAngularBasis := by
    simpa only [hU] using hvalue
  exact hF.symm.trans (P.forcing_eq_finite_of_height hl hr h04 href hsector
    ha hc hpot s hvalueU hweak)

/-- The original source and the actual cubic map give the local current
Green identity on the finite height core, with both true weighted endpoint
terms. Neither the original PDE nor forcing angular support is assumed. -/
theorem n06N05_positive_finite_relative_green
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (hm : K.positive m = true)
    (P : N06UnitWeakGraphData a c pot U F κ)
    (hU : U 0 = u.val.1.1 m)
    (hF : (F 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06ReferenceCanonicalForcing D S C K u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m)
    (hl : K.left m = 0) (hr : K.right m = 1)
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hpot : Continuous pot)
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a p.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c p.1) (canonicalOpen S K m))
    (hepot : EqOn (K.potential (C.referenceState, 0) m)
      (fun p => pot p.1) (canonicalOpen S K m))
    {scale : ℕ → ℝ} {δ : ℝ}
    (hcoeff : N06PositiveCubicControl K b scale δ
      (fun n => (K.dividedDifference z n).a) (fun n => (K.dividedDifference z n).b)
      (fun n => (K.dividedDifference z n).c))
    (s : Finset ℕ)
    (hvalue : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s P.modes referenceAngularBasis)
    (G Fcur : CanonicalSequence S K)
    (hsource : (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, G m p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u.val.1.1 m p * n06PositiveCubicTestOperator K
          (fun n => (K.dividedDifference z n).a) (fun n => (K.dividedDifference z n).b)
          (fun n => (K.dividedDifference z n).c) m ψ p ∂canonicalMeasure S K m)
    (hφ : RadialTest D φ)
    (Q : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ)) :
    (∫ p, n06CurrentRemainderSource D S C L K z u.val.1 Fcur m p *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a (K.right m) * (Q.value (K.right m, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.right m, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (K.right m, θ) *
              Q.radial (K.right m, θ)) -
        a (K.left m) * (Q.value (K.left m, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.left m, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (K.left m, θ) *
              Q.radial (K.left m, θ)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hforcing := n06N05_positive_finite_referenceForcing hS h u hm P hU hF
    hl hr ha hc hpot hcd hea heb hec hepot s hvalue
  have hrem := n06_currentRelativeSource_positive_remainder_ae u.val.1
    (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G Fcur m hm hsource
  have hleft :
      (∫ p, n06CurrentRemainderSource D S C L K z u.val.1 Fcur m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) =
      ∫ p, (-r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p +
        G m p - (K.potential z m p - K.potential (C.referenceState, 0) m p) *
          r11bFiniteSynthesis s P.modes referenceAngularBasis p) *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [hrem, hforcing, hvalue] with p hp hf hv
    rw [hp, hf, hv]
  have hcubic : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, G m p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) (K.dividedDifference z m).a
            (K.dividedDifference z m).b (K.dividedDifference z m).c) ψ p
              ∂canonicalMeasure S K m := by
    intro ψ hψ
    refine (hweak ψ hψ).trans ?_
    apply integral_congr_ae
    filter_upwards [hvalue] with p hp
    simp only [n06PositiveCubicTestOperator, hm, ↓reduceIte, hp]
  rw [hleft]
  simpa only [hl, hr] using P.current_positive_fullPeriod_green Q hT hS h01 h03 h04
    hz hs hm hl hr ha hc hpot hcd hea heb hec hepot hcoeff s (G m) hcubic hφ

end ContinuousFlexibility.Analysis
