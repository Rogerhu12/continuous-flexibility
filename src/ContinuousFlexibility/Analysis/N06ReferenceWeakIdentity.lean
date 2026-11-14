module

public import ContinuousFlexibility.Analysis.N05LocalEvenTests
public import ContinuousFlexibility.Analysis.N06CubicDifferential
public import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# The corrected reference operator in the original physical weak pairing

The N03 identity on the actual height space determines the operator on every
smooth germ off the reflection circles. Those circles form a countable set
of angular values. Removing them in the angular integral proves the full
physical weak identity at every radius of the open annulus, including the
turning radii and artificial cuts. No regularity of the unknown field or
extra regularity of the corrected coefficients is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The exceptional angular set in the actual local-height test theorem
has zero Lebesgue measure. -/
theorem n06_ae_nonreflection_angle :
    ∀ᵐ θ : ℝ ∂volume,
      θ ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2)) :=
  (Set.countable_range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))).ae_notMem volume

theorem n06_radialAngularMean_congr_ae {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume] g) : radialAngularMean f = radialAngularMean g := by
  unfold radialAngularMean
  congr 1
  exact intervalIntegral.integral_congr_ae (hfg.mono fun _ hx _ => hx)

/-- The original nonlinear coefficients give the genuine radial differential
expression at the selected reference state. -/
theorem n06_originalReference_testOperator
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : IsAccumulatingProfile D) (href : referenceStateConditions D S C)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) {p : PolarPoint}
    (hr : p.1 ≠ 0) :
    divergenceOperator (originalCoefficients D S C (C.referenceState, 0)) φ p =
      n06ReferenceTestOperator D φ p := by
  let A0 : SymmetricCoefficients :=
    ⟨fun q => D.w q.1, fun _ => 0, fun q => deriv D.w q.1 / q.1⟩
  have ha : (originalCoefficients D S C (C.referenceState, 0)).a =ᶠ[𝓝 p] A0.a :=
    Eventually.of_forall fun q => (n05_originalCoefficients_reference hD href q).1
  have hb : (originalCoefficients D S C (C.referenceState, 0)).b =ᶠ[𝓝 p] A0.b :=
    Eventually.of_forall fun q => (n05_originalCoefficients_reference hD href q).2.1
  have hc : (originalCoefficients D S C (C.referenceState, 0)).c =ᶠ[𝓝 p] A0.c :=
    Eventually.of_forall fun q => (n05_originalCoefficients_reference hD href q).2.2
  calc
    _ = divergenceOperator A0 φ p := n06_divergenceOperator_congr_germ φ ha hb hc
    _ = _ := reference_divergence_eq_radialPDE hD.choose_spec.1.2.2.1.1 hφ hr

/-- At each actual annular radius, the corrected operator and radial
operator agree for almost every angle. -/
theorem n06_correctedReference_testOperator_ae_angle
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {r : ℝ} (hr : r ∈ radialCore D) :
    (fun θ => divergenceOperator (L.coefficients (C.referenceState, 0)) φ (r, θ))
      =ᵐ[volume] (fun θ => n06ReferenceTestOperator D φ (r, θ)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1
  have hD : IsAccumulatingProfile D := h01.1.1
  have hr0 : r ≠ 0 := (hD.choose_spec.1.1.trans hr.1).ne'
  filter_upwards [n06_ae_nonreflection_angle] with θ hθ
  have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ θ⟩
  have hlocal := n05_reference_correctionOperator_eq_local hT hS h
    isOpen_univ hφ.contDiffOn (mem_univ (r, θ)) hp hθ
  exact hlocal.symm.trans
    (n06_originalReference_testOperator hD h01.2.2.1 hφ hr0)

/-- An arbitrary physical representative can multiply the almost-everywhere
operator identity; the representative need not be smooth or measurable. -/
theorem n06_correctedReference_angular_pairing
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (η : PolarPoint → ℝ) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {r : ℝ} (hr : r ∈ radialCore D) :
    radialAngularMean (fun θ =>
      η (r, θ) * divergenceOperator (L.coefficients (C.referenceState, 0)) φ (r, θ)) =
    radialAngularMean (fun θ => η (r, θ) * n06ReferenceTestOperator D φ (r, θ)) := by
  apply n06_radialAngularMean_congr_ae
  filter_upwards [n06_correctedReference_testOperator_ae_angle hT hS h hφ hr]
    with θ hθ
  exact congrArg (fun t : ℝ => η (r, θ) * t) hθ

/-- The full-period pairing in `PerturbedCanonicalRelation` is exactly the
radial weak pairing of the original reference graph. -/
theorem n06_correctedReference_weak_pairing
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (η : PolarPoint → ℝ) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      η (r, θ) * divergenceOperator (L.coefficients (C.referenceState, 0)) φ (r, θ))) =
      radialWeakPairing D η φ := by
  have hD : IsAccumulatingProfile D := h.1.1.1.1
  apply intervalIntegral.integral_congr_Ioo_of_le hD.choose_spec.1.2.1.le
  intro r hr
  exact n06_correctedReference_angular_pairing hT hS h η hφ hr

end ContinuousFlexibility.Statements
