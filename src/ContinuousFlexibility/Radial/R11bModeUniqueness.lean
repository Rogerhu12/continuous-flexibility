import ContinuousFlexibility.Radial.R11bHomogeneousMode
import ContinuousFlexibility.Radial.R11bWeakModes
import ContinuousFlexibility.Analysis.IntervalWeakPotential

/-!
# Modal uniqueness for strict interior physical tests

The physical graph initially supplies only tests whose topological support
lies inside the core. Compression extends that equation to the exact frozen
modal test domain. The given inverse then proves uniqueness without any
assumption on the output cell exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem r11b_homogeneous_mode_eq_zero_of_strict {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) {j : ℕ}
    {G : RadialModePair D →L[ℝ] RadialModePair D} (hG : ModeInverseProperties D j G)
    {u : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (radialCore D))) (κ : ℝ)
    (hκ : j ≠ 2 → κ = 0)
    (hrow : j = 2 → (∫ r in D.a..D.b, referenceColumn D r * u r) = 0)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
        (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) +
          κ * (∫ r in D.a..D.b, referenceColumn D r * φ r) = 0) :
    u =ᵐ[volume.restrict (radialCore D)] 0 ∧ κ = 0 := by
  apply r11b_homogeneous_mode_eq_zero hgeom hG
    (r11b_memLp_radialHilbert_of_memLp hgeom hu) κ hκ hrow
  intro ψ hψ hψc hψs
  have hV : Continuous (fun r => (j : ℝ) ^ 2 * deriv D.w r / r) := by
    simp_rw [mul_div_assoc]
    exact continuous_const.mul (r11b_continuous_flat_deriv_div hgeom.1 hgeom.2.2.1)
  have hstrict : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
        (∫ r in D.a..D.b, u r *
          (deriv (fun t => D.w t * deriv φ t) r -
            ((j : ℝ) ^ 2 * deriv D.w r / r) * φ r)) +
          κ * (∫ r in D.a..D.b, referenceColumn D r * φ r) =
            ∫ _r in D.a..D.b, (0 : ℝ) := by
    intro φ hφ hφc hφs
    simpa only [radialJacobi, intervalIntegral.integral_zero] using heq φ hφ hφc hφs
  have hzero : MemLp (fun _ : ℝ => (0 : ℝ)) 2
      (volume.restrict (radialCore D)) :=
    MemLp.ae_eq (Lp.coeFn_zero ℝ 2 (volume.restrict (radialCore D))) (Lp.memLp 0)
  have h := extend_weak_potential_tests_interval hgeom.2.1 hu hzero
    hgeom.2.2.1.1 hV (r11b_continuous_referenceColumn hgeom hborder) κ
    (by simpa only [zero_mul, radialCore] using hstrict) hψ hψc hψs
  simpa only [radialJacobi, zero_mul, intervalIntegral.integral_zero] using h

theorem r11b_graph_mode_unique {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ γ' M₀ M₀' M₁ M₁' : ℝ} (hγ : 0 < γ) (hγ' : 0 < γ')
    {U V : RadialUnknown} {F : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F)
    (hVF : ReferenceGraph D γ' M₀' M₁' V F)
    {j : ℕ} (hj : 0 < j)
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) :
    referenceMode U.1 j =ᵐ[volume.restrict (radialCore D)] referenceMode V.1 j ∧
      (j = 2 → U.2 = V.2) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hu := (r11b_referenceMode_L2_bound
    (r11b_output_memLp hD hborder hγ hUF.1) j hj).1
  have hv := (r11b_referenceMode_L2_bound
    (r11b_output_memLp hD hborder hγ' hVF.1) j hj).1
  let u : ℝ → ℝ := fun r => referenceMode U.1 j r - referenceMode V.1 j r
  have hdiff : MemLp u 2 (volume.restrict (radialCore D)) := by
    apply MemLp.ae_eq _ (hu.sub hv)
    exact Filter.Eventually.of_forall fun _ => rfl
  let κ : ℝ := if j = 2 then U.2 - V.2 else 0
  have hrow : j = 2 →
      (∫ r in D.a..D.b, referenceColumn D r * u r) = 0 := by
    intro hj2
    have hg := r11b_continuous_referenceColumn hgeom hborder
    have hUi := intervalIntegrable_mul_continuous hgeom.2.1.le hu hg
    have hVi := intervalIntegrable_mul_continuous hgeom.2.1.le hv hg
    have heq : (fun r => referenceColumn D r * u r) =
        (fun r => referenceMode U.1 j r * referenceColumn D r -
          referenceMode V.1 j r * referenceColumn D r) := by
      funext r
      dsimp [u]
      ring
    rw [heq, intervalIntegral.integral_sub hUi hVi]
    have hUr := hUF.2.2.1
    have hVr := hVF.2.2.1
    change (∫ r in D.a..D.b, referenceColumn D r * referenceMode U.1 2 r) = F.2 at hUr
    change (∫ r in D.a..D.b, referenceColumn D r * referenceMode V.1 2 r) = F.2 at hVr
    have hUr' : (∫ r in D.a..D.b, referenceMode U.1 j r * referenceColumn D r) = F.2 := by
      simpa only [hj2, mul_comm] using hUr
    have hVr' : (∫ r in D.a..D.b, referenceMode V.1 j r * referenceColumn D r) = F.2 := by
      simpa only [hj2, mul_comm] using hVr
    rw [hUr', hVr', sub_self]
  have heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
        (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w φ r) +
          κ * (∫ r in D.a..D.b, referenceColumn D r * φ r) = 0 := by
    intro φ hφ hφc hφs
    have hL := r11b_continuous_radialJacobi hgeom.1 hgeom.2.2.1 hφ ((j : ℝ) ^ 2)
    have hUi := intervalIntegrable_mul_continuous hgeom.2.1.le hu hL
    have hVi := intervalIntegrable_mul_continuous hgeom.2.1.le hv hL
    change (∫ r in D.a..D.b,
      (referenceMode U.1 j r - referenceMode V.1 j r) *
        radialJacobi ((j : ℝ) ^ 2) D.w φ r) + _ = 0
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub hUi hVi]
    have hUeq := r11b_referenceGraph_mode_equation hgeom hUF j hj hφ hφc hφs
    have hVeq := r11b_referenceGraph_mode_equation hgeom hVF j hj hφ hφc hφs
    by_cases hj2 : j = 2
    · dsimp only [κ]
      simp only [hj2, ite_true] at hUeq hVeq ⊢
      linarith
    · dsimp only [κ]
      simp only [hj2, ite_false, zero_mul, add_zero] at hUeq hVeq ⊢
      linarith
  obtain ⟨hz, hκ⟩ := r11b_homogeneous_mode_eq_zero_of_strict hgeom hborder hG hdiff κ
    (fun hj2 => if_neg hj2) hrow heq
  refine ⟨?_, ?_⟩
  · filter_upwards [hz] with r hr
    change referenceMode U.1 j r - referenceMode V.1 j r = 0 at hr
    exact sub_eq_zero.mp hr
  · intro hj2
    have h : U.2 - V.2 = 0 := by simpa only [κ, hj2, ite_true] using hκ
    exact sub_eq_zero.mp h

end ContinuousFlexibility.Radial
