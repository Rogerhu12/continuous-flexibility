import ContinuousFlexibility.Radial.R11bModeUniqueness

/-!
# Proportionality of actual reference-graph modes

A proportional source mode determines the proportional output mode, even
when the two physical graphs use different positive weight exponents. In
the bordered mode, the scalar row datum must have the same proportionality.
The proof subtracts the actual weak equations and applies modal uniqueness.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem r11b_graph_mode_scaling {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ γ' M₀ M₀' M₁ M₁' : ℝ} (hγ : 0 < γ) (hγ' : 0 < γ')
    {U V : RadialUnknown} {F K : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F)
    (hVK : ReferenceGraph D γ' M₀' M₁' V K)
    {j : ℕ} (hj : 0 < j)
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) (s : ℝ)
    (hsource : referenceMode K.1 j
      =ᵐ[volume.restrict (radialCore D)] (fun r => s * referenceMode F.1 j r))
    (hsourceRow : j = 2 → K.2 = s * F.2) :
    referenceMode V.1 j
      =ᵐ[volume.restrict (radialCore D)] (fun r => s * referenceMode U.1 j r) ∧
      (j = 2 → V.2 = s * U.2) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hu := (r11b_referenceMode_L2_bound
    (r11b_output_memLp hD hborder hγ hUF.1) j hj).1
  have hv := (r11b_referenceMode_L2_bound
    (r11b_output_memLp hD hborder hγ' hVK.1) j hj).1
  let u : ℝ → ℝ := fun r => referenceMode V.1 j r - s * referenceMode U.1 j r
  have hdiff : MemLp u 2 (volume.restrict (radialCore D)) := by
    apply MemLp.ae_eq _ (hv.sub (hu.const_smul s))
    exact Filter.Eventually.of_forall fun _ => rfl
  let ell : ℝ := if j = 2 then V.2 - s * U.2 else 0
  have hrow : j = 2 →
      (∫ r in D.a..D.b, referenceColumn D r * u r) = 0 := by
    intro hj2
    have hg := r11b_continuous_referenceColumn hgeom hborder
    have hUi := intervalIntegrable_mul_continuous hgeom.2.1.le hu hg
    have hVi := intervalIntegrable_mul_continuous hgeom.2.1.le hv hg
    have hpoint : (fun r => referenceColumn D r * u r) =
        (fun r => referenceMode V.1 j r * referenceColumn D r -
          s * (referenceMode U.1 j r * referenceColumn D r)) := by
      funext r
      dsimp only [u]
      ring
    rw [hpoint, intervalIntegral.integral_sub hVi (hUi.const_mul s),
      intervalIntegral.integral_const_mul]
    have hUr := hUF.2.2.1
    have hVr := hVK.2.2.1
    change (∫ r in D.a..D.b, referenceColumn D r * referenceMode U.1 2 r) = F.2 at hUr
    change (∫ r in D.a..D.b, referenceColumn D r * referenceMode V.1 2 r) = K.2 at hVr
    have hUr' : (∫ r in D.a..D.b, referenceMode U.1 j r * referenceColumn D r) = F.2 := by
      simpa only [hj2, mul_comm] using hUr
    have hVr' : (∫ r in D.a..D.b, referenceMode V.1 j r * referenceColumn D r) = K.2 := by
      simpa only [hj2, mul_comm] using hVr
    rw [hVr', hUr', hsourceRow hj2, sub_self]
  have hμ : (volume : Measure ℝ).restrict (radialCore D) =
      volume.restrict (Ioc D.a D.b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hsourceIoc : referenceMode K.1 j
      =ᵐ[volume.restrict (Ioc D.a D.b)] (fun r => s * referenceMode F.1 j r) := by
    rwa [← hμ]
  have heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
        (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) +
          ell * (∫ r in D.a..D.b, referenceColumn D r * φ r) = 0 := by
    intro φ hφ hφc hφs
    have hL := r11b_continuous_radialJacobi hgeom.1 hgeom.2.2.1 hφ ((j : ℝ) ^ 2)
    have hUi := intervalIntegrable_mul_continuous hgeom.2.1.le hu hL
    have hVi := intervalIntegrable_mul_continuous hgeom.2.1.le hv hL
    have hpoint : (fun r => u r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) =
        (fun r => referenceMode V.1 j r * radialJacobi ((j : ℝ) ^ 2) D.w φ r -
          s * (referenceMode U.1 j r * radialJacobi ((j : ℝ) ^ 2) D.w φ r)) := by
      funext r
      dsimp only [u]
      ring
    rw [hpoint, intervalIntegral.integral_sub hVi (hUi.const_mul s),
      intervalIntegral.integral_const_mul]
    have hsourcePair :
        (∫ r in D.a..D.b, referenceMode K.1 j r * φ r) =
          s * (∫ r in D.a..D.b, referenceMode F.1 j r * φ r) := by
      simp only [intervalIntegral.integral_of_le hgeom.2.1.le]
      calc
        _ = ∫ r in Ioc D.a D.b, s * (referenceMode F.1 j r * φ r) := by
          apply integral_congr_ae
          filter_upwards [hsourceIoc] with r hr
          rw [hr]
          ring
        _ = _ := integral_const_mul _ _
    have hUeq := r11b_referenceGraph_mode_equation hgeom hUF j hj hφ hφc hφs
    have hVeq := r11b_referenceGraph_mode_equation hgeom hVK j hj hφ hφc hφs
    rw [hsourcePair] at hVeq
    by_cases hj2 : j = 2
    · subst j
      simp only [if_pos rfl] at hUeq hVeq
      dsimp only [ell]
      simp only [if_pos rfl]
      have hscaled := congrArg (fun t : ℝ => s * t) hUeq
      nlinarith only [hVeq, hscaled]
    · simp only [if_neg hj2, zero_mul, add_zero] at hUeq hVeq
      dsimp only [ell]
      rw [if_neg hj2]
      have hscaled := congrArg (fun t : ℝ => s * t) hUeq
      nlinarith only [hVeq, hscaled]
  obtain ⟨hz, hEll⟩ := r11b_homogeneous_mode_eq_zero_of_strict hgeom hborder hG hdiff ell
    (fun hj2 => if_neg hj2) hrow heq
  refine ⟨?_, ?_⟩
  · filter_upwards [hz] with r hr
    change referenceMode V.1 j r - s * referenceMode U.1 j r = 0 at hr
    exact sub_eq_zero.mp hr
  · intro hj2
    have h : V.2 - s * U.2 = 0 := by
      simpa only [ell, hj2, ite_true] using hEll
    exact sub_eq_zero.mp h

end

end ContinuousFlexibility.Radial
