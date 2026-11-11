import ContinuousFlexibility.Radial.InnerRadialSmoothGreen
import ContinuousFlexibility.Radial.InnerRadialWeakLinearity

/-!
# Smooth Green tests against the actual closed first-order domain

The classical identity extends in the test variable by continuity to the
physical zero-endpoint closure. Adding the fixed affine lift restores
exactly the two canonical boundary traces. The smooth solution, signed
potential and source remain the original physical ones.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

section Green

variable (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
  {a b j : ℝ} (hab : a < b) (ha : 0 < a)
  (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
  {u : ℝ → ℝ} (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r)
  {Q : InnerRadialH1Pair D} {V F C : RadialModeL2 D} (scalar : ℝ)
  (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
  (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
    (Ioo a b).indicator (innerGapGradientField u))
  (hV : InnerRadialPotentialClass D j a b Q.1 V)
  (hF : ((F - scalar • C : RadialModeL2 D) : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
    (Ioo a b).indicator
      (fun r => -radialJacobi (j ^ 2) D.w u r / (12 * D.w r / r ^ 2)))

include hw hab ha hcore hpos hu hQu hQd hV hF

theorem matchedInner_smoothResidual_zero {T : InnerRadialH1Pair D}
    (hT : T ∈ innerRadialH1Zero D a b) :
    innerRadialWeakResidual D Q V F C scalar T = 0 := by
  have hclosed : IsClosed {T : InnerRadialH1Pair D |
      innerRadialWeakResidual D Q V F C scalar T = 0} :=
    isClosed_eq (innerRadialWeakResidual_continuous D Q V F C scalar) continuous_const
  apply (closure_minimal (t := {T : InnerRadialH1Pair D |
      innerRadialWeakResidual D Q V F C scalar T = 0}) ?_ hclosed)
    ((mem_innerRadialH1Zero D a b T).mp hT)
  rintro R ⟨p, hp, _, hs, hRu, hRd⟩
  have hpa : p a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hs h).1)
  have hpb : p b = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl b) (hs h).2)
  have h := innerRadialWeakResidual_smooth D hw hab.le ha hcore hpos hu
    (fun _ _ => hp.contDiffAt) scalar hQu hQd hRu hRd hV hF
  simpa only [hpa, hpb, zero_mul, sub_self] using h

/-- Green's identity for a smooth physical field tested against any
element of the actual H¹ domain, with its proved canonical traces. -/
theorem matchedInner_smoothResidual_domain {T : InnerRadialH1Pair D}
    (hT : T ∈ innerRadialH1Domain D hw.continuous ha hcore hpos) :
    innerRadialWeakResidual D Q V F C scalar T =
      innerRadialH1Trace D hw.continuous ha hcore hpos T 1 * (D.w b * deriv u b) -
        innerRadialH1Trace D hw.continuous ha hcore hpos T 0 * (D.w a * deriv u a) := by
  have hz := matchedInner_smoothResidual_zero D hw hab ha hcore hpos hu scalar
    hQu hQd hV hF ((mem_innerRadialH1Domain D hw.continuous ha hcore hpos T).mp hT)
  rw [map_sub] at hz
  rw [sub_eq_zero] at hz
  rw [hz]
  exact innerRadialWeakResidual_affineLift D hw hab ha hcore hpos hu scalar
    hQu hQd hV hF (innerRadialH1Trace D hw.continuous ha hcore hpos T)

end Green

end ContinuousFlexibility.Radial
