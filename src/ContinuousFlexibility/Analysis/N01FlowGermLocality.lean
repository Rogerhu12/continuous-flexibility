module

public import ContinuousFlexibility.Analysis.N01FlowLocality
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Characteristic locality modulo additive height constants

Every actual coefficient uses height derivatives. An additive constant
therefore leaves it unchanged, including for the total Fréchet
derivative convention. Local profile equality makes the two actual
radial primitives differ only by a constant on the connected component.
These facts give the precise locality needed for trace and control
directions in the supplied physical state space.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace ContinuousFlexibility

theorem heightRadial_add_constant (f : PolarPoint → ℝ) (c : ℝ) :
    heightRadial (fun p => f p + c) = heightRadial f := by
  funext p
  simp only [heightRadial, radialPartial, fderiv_add_const]

theorem heightAngular_add_constant (f : PolarPoint → ℝ) (c : ℝ) :
    heightAngular (fun p => f p + c) = heightAngular f := by
  funext p
  simp only [heightAngular, angularPartial, fderiv_add_const]

theorem polar_coefficients_height_add_constant
    (w : ℝ → ℝ) (f : PolarPoint → ℝ) (c : ℝ) (p : PolarPoint) :
    polarLinearA w (fun y => f y + c) p = polarLinearA w f p ∧
      polarLinearB w (fun y => f y + c) p = polarLinearB w f p ∧
      polarCorrectedC w (fun y => f y + c) p = polarCorrectedC w f p := by
  simp only [polarLinearA, polarLinearB, polarCorrectedC, polarScale, polarDiscriminant,
    heightRadial_add_constant, heightAngular_add_constant, and_self]

theorem polar_coefficients_eq_of_eventuallyEq_add_constant
    {w v : ℝ → ℝ} {f g : PolarPoint → ℝ} {p : PolarPoint} (c : ℝ)
    (hw : w =ᶠ[𝓝 p.1] v) (hf : f =ᶠ[𝓝 p] (fun y => g y + c)) :
    polarLinearA w f p = polarLinearA v g p ∧
      polarLinearB w f p = polarLinearB v g p ∧
      polarCorrectedC w f p = polarCorrectedC v g p := by
  obtain ⟨hA, hB, hC⟩ := polar_coefficients_eq_of_eventuallyEq hw hf
  obtain ⟨hA', hB', hC'⟩ := polar_coefficients_height_add_constant v g c p
  exact ⟨hA.trans hA', hB.trans hB', hC.trans hC'⟩

end ContinuousFlexibility

namespace ContinuousFlexibility.Statements

local instance n01FlowGermLocalityRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

theorem CutoffConditions.constant_on_negative_component
    {D : ReferenceData} {χ : ℝ → ℝ} (hχ : CutoffConditions D χ)
    {l r : ℝ} (hnegative : ∀ t ∈ Ioo l r, deriv D.w t < 0) :
    ∃ c : ℝ, ∀ t ∈ Ioo l r, χ t = c := by
  obtain ⟨K, _, _, hpositive, hzero⟩ := hχ.2.2
  apply isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo l r).isPreconnected
    (hχ.1.differentiable (by simp)).differentiableOn
  intro t ht
  apply hzero t
  intro htK
  exact (not_lt_of_ge (hpositive t htK).le) (hnegative t ht)

theorem N01Properties.minusFlow_eq_of_local_profile_height
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z z' : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hz' : z' ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hq : z.2 = z'.2) (m : ℕ)
    (hw : EqOn (stateProfile D S C z.1) (stateProfile D S C z'.1)
      (Ioo (C.left m) (C.right m))) (c : ℝ)
    (hu : ∀ t ∈ Ioo (C.left m) (C.right m), ∀ θ,
      stateU S z.1 (t, θ) = stateU S z'.1 (t, θ) + c) (θ : ℝ) :
    EqOn (fun r => C.minusFlow z m r θ) (fun r => C.minusFlow z' m r θ)
      (Icc (C.left m) (C.right m)) := by
  have hW := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hW' := contDiff_stateProfile_of_n01 hS hT hN z'.1
  have hp (r : ℝ) :
      HasDerivAt (stateRadialHeight D S C z.1) (stateProfile D S C z.1 r) r :=
    intervalIntegral.integral_hasDerivAt_right (hW.continuous.intervalIntegrable D.b r)
      hW.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hW.continuous.continuousAt
  have hp' (r : ℝ) :
      HasDerivAt (stateRadialHeight D S C z'.1) (stateProfile D S C z'.1 r) r :=
    intervalIntegral.integral_hasDerivAt_right (hW'.continuous.intervalIntegrable D.b r)
      hW'.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hW'.continuous.continuousAt
  have hderiv : EqOn (deriv (stateRadialHeight D S C z.1))
      (deriv (stateRadialHeight D S C z'.1)) (Ioo (C.left m) (C.right m)) := by
    intro r hr
    rw [(hp r).deriv, (hp' r).deriv]
    exact hw hr
  obtain ⟨a, ha⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq
    (convex_Ioo (C.left m) (C.right m)).isPreconnected
    (fun r _ => (hp r).differentiableAt.differentiableWithinAt)
    (fun r _ => (hp' r).differentiableAt.differentiableWithinAt) hderiv
  apply hN.minusFlow_eq_of_characteristic_speed hS hT hz hz' hsector m θ
  intro r hr ψ
  have hWgerm : stateProfile D S C z.1 =ᶠ[𝓝 r] stateProfile D S C z'.1 := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact hw ht
  have hheight : stateHeight D S C z =ᶠ[𝓝 (r, ψ)]
      (fun p => stateHeight D S C z' p + (a + z'.2 * c)) := by
    filter_upwards [continuousAt_fst.eventually (isOpen_Ioo.mem_nhds hr)] with p hpI
    simp only [stateHeight, ha hpI, hq, hu p.1 hpI p.2]
    ring
  obtain ⟨hA, hB, hC⟩ := polar_coefficients_eq_of_eventuallyEq_add_constant
    (a + z'.2 * c) hWgerm hheight
  simp only [minusCharacteristicSpeed, originalCoefficients, hA, hB, hC]

end ContinuousFlexibility.Statements
