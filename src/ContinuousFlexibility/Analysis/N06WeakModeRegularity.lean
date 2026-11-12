import ContinuousFlexibility.Radial.WeakDivergenceRegularity
import ContinuousFlexibility.Analysis.IntervalWeakPotential
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Regularity of the actual weak modal equation

An L2 distributional solution on a finite interval has a C1 representative,
an absolutely continuous first derivative, and an L2 second derivative when
the smooth radial leading coefficient does not vanish on the closed interval.
The representative and its derivatives are obtained from the actual weak
equation. No derivative of the original measurable representative is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

/-- A measurable coefficient continuous on the closed interval is essentially bounded
for the measure of its open interior. -/
theorem n06_memLp_top_of_continuousOn_Icc {l r : ℝ} {p : ℝ → ℝ}
    (hp : ContinuousOn p (Icc l r))
    (hm : AEStronglyMeasurable p (volume.restrict (Ioo l r))) :
    MemLp p ∞ (volume.restrict (Ioo l r)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hp.norm
  apply memLp_top_of_bound hm M
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hM ⟨x, mem_Icc_of_Ioo hx, rfl⟩

/-- Multiplication by a continuous coefficient preserves L2 on a finite interval. -/
theorem n06_interval_memLp_mul_continuous {l r : ℝ} {u p : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo l r))) (hp : Continuous p) :
    MemLp (fun x => p x * u x) 2 (volume.restrict (Ioo l r)) :=
  (n06_memLp_top_of_continuousOn_Icc hp.continuousOn hp.aestronglyMeasurable).fun_mul hu

/-- The closed-interval weak divergence representative has two actual L2 derivatives.
Its first derivative is absolutely continuous all the way to both endpoints. -/
theorem n06_weak_divergence_L2_regular {l r : ℝ} (hlr : l < r)
    {a u g : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (han : ∀ x ∈ Icc l r, a x ≠ 0)
    (hu : MemLp u 2 (volume.restrict (Ioo l r)))
    (hg : MemLp g 2 (volume.restrict (Ioo l r)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo l r →
        (∫ x in l..r, u x * deriv (fun y => a y * deriv φ y) x) =
          ∫ x in l..r, g x * φ x) :
    ∃ v : ℝ → ℝ,
      u =ᵐ[volume.restrict (Ioo l r)] v ∧
      ContDiff ℝ 1 v ∧
      AbsolutelyContinuousOnInterval (deriv v) l r ∧
      MemLp v 2 (volume.restrict (Ioo l r)) ∧
      MemLp (deriv v) 2 (volume.restrict (Ioo l r)) ∧
      MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo l r)) ∧
      (∀ᵐ x ∂volume.restrict (Ioo l r),
        a x * deriv (deriv v) x + deriv a x * deriv v x = g x) ∧
      (deriv (fun x => a x * deriv v x) =ᵐ[volume.restrict (Ioo l r)] g) := by
  have hui : IntervalIntegrable u volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr.le).mpr
      (interval_memLp_integrable hu)
  have hgi : IntervalIntegrable g volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr.le).mpr
      (interval_memLp_integrable hg)
  obtain ⟨v, C, hv, huv, _hflux, hfluxAC, hfluxD⟩ :=
    ContinuousFlexibility.Radial.exists_contDiff_representative_of_weak_divergence
      hlr hui hgi ha han hweak
  have ha₁ : ContDiff ℝ 1 a := ha.of_le (by simp)
  have hinv : ContDiffOn ℝ 1 (fun x => (a x)⁻¹) (Icc l r) :=
    ha₁.contDiffOn.inv han
  have hinvAC : AbsolutelyContinuousOnInterval (fun x => (a x)⁻¹) l r := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hlr.le] using hinv
  have hvdAC : AbsolutelyContinuousOnInterval (deriv v) l r := by
    apply (hfluxAC.fun_mul hinvAC).congr
    intro x hx
    rw [uIcc_of_le hlr.le] at hx
    change (a x * deriv v x) * (a x)⁻¹ = deriv v x
    field_simp [han x hx] <;> ring
  have hvd : Continuous (deriv v) := hv.continuous_deriv le_rfl
  have hv₂ : MemLp v 2 (volume.restrict (Ioo l r)) :=
    (memLp_congr_ae huv).mp hu
  have hvd₂ : MemLp (deriv v) 2 (volume.restrict (Ioo l r)) :=
    interval_memLp_of_continuous hvd
  have hdiff : ∀ᵐ x ∂volume.restrict (Ioo l r), DifferentiableAt ℝ (deriv v) x := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hvdAC.ae_differentiableAt] with x hx hxi
    apply hx
    simpa only [uIcc_of_le hlr.le] using mem_Icc_of_Ioo hxi
  have hode : ∀ᵐ x ∂volume.restrict (Ioo l r),
      a x * deriv (deriv v) x + deriv a x * deriv v x = g x := by
    filter_upwards [hdiff, hfluxD] with x hx heq
    have hd : deriv (fun y => a y * deriv v y) x =
        deriv a x * deriv v x + a x * deriv (deriv v) x :=
      ((ha.differentiable (by simp) x).hasDerivAt.fun_mul hx.hasDerivAt).deriv
    rw [hd] at heq
    linarith only [heq]
  have hsecond : deriv (deriv v) =ᵐ[volume.restrict (Ioo l r)]
      (fun x => (g x - deriv a x * deriv v x) / a x) := by
    filter_upwards [hode, ae_restrict_mem measurableSet_Ioo] with x hx hxi
    apply (eq_div_iff (han x (mem_Icc_of_Ioo hxi))).mpr
    nlinarith only [hx]
  have hnum : MemLp (fun x => g x - deriv a x * deriv v x) 2
      (volume.restrict (Ioo l r)) :=
    hg.sub (interval_memLp_of_continuous ((ha.continuous_deriv (by simp)).mul hvd))
  have hinvTop : MemLp (fun x => (a x)⁻¹) ∞ (volume.restrict (Ioo l r)) :=
    n06_memLp_top_of_continuousOn_Icc hinv.continuousOn
      ha.continuous.measurable.inv.aestronglyMeasurable
  have hquot : MemLp (fun x => (g x - deriv a x * deriv v x) / a x) 2
      (volume.restrict (Ioo l r)) := by
    have hprod : MemLp (fun x => (g x - deriv a x * deriv v x) * (a x)⁻¹) 2
        (volume.restrict (Ioo l r)) := hnum.fun_mul hinvTop
    simpa only [div_eq_mul_inv] using hprod
  have hvdd₂ : MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo l r)) :=
    (memLp_congr_ae hsecond).mpr hquot
  exact ⟨v, huv, hv, hvdAC, hv₂, hvd₂, hvdd₂, hode, hfluxD⟩

/-- The genuine weak modal equation with L2 forcing supplies the same representative,
its endpoint regularity, and the original equation almost everywhere. -/
theorem n06_weak_mode_L2_regular {l r : ℝ} (hlr : l < r)
    {a c V u F : ℝ → ℝ} (j : ℝ)
    (ha : ContDiff ℝ ∞ a) (han : ∀ x ∈ Icc l r, a x ≠ 0)
    (hc : Continuous c) (hV : Continuous V)
    (hu : MemLp u 2 (volume.restrict (Ioo l r)))
    (hF : MemLp F 2 (volume.restrict (Ioo l r)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo l r →
        (∫ x in l..r, u x * (-deriv (fun y => a y * deriv φ y) x +
          (j ^ 2 * c x + V x) * φ x)) = ∫ x in l..r, F x * φ x) :
    ∃ v : ℝ → ℝ,
      u =ᵐ[volume.restrict (Ioo l r)] v ∧
      ContDiff ℝ 1 v ∧
      AbsolutelyContinuousOnInterval (deriv v) l r ∧
      MemLp v 2 (volume.restrict (Ioo l r)) ∧
      MemLp (deriv v) 2 (volume.restrict (Ioo l r)) ∧
      MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo l r)) ∧
      (∀ᵐ x ∂volume.restrict (Ioo l r),
        -deriv (fun y => a y * deriv v y) x +
          j ^ 2 * c x * v x + V x * v x = F x) ∧
      (∀ᵐ x ∂volume.restrict (Ioo l r),
        -(a x * deriv (deriv v) x + deriv a x * deriv v x) +
          j ^ 2 * c x * v x + V x * v x = F x) := by
  let P : ℝ → ℝ := fun x => j ^ 2 * c x + V x
  let g : ℝ → ℝ := fun x => P x * u x - F x
  have hP : Continuous P := (continuous_const.mul hc).add hV
  have hg : MemLp g 2 (volume.restrict (Ioo l r)) :=
    (n06_interval_memLp_mul_continuous hu hP).sub hF
  have hdiv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo l r →
        (∫ x in l..r, u x * deriv (fun y => a y * deriv φ y) x) =
          ∫ x in l..r, g x * φ x := by
    intro φ hφ hφc hφs
    have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    have hflux : ContDiff ℝ ∞ (fun y => a y * deriv φ y) := ha.mul hφd
    have hi₁ : IntervalIntegrable
        (fun x => u x * deriv (fun y => a y * deriv φ y) x) volume l r :=
      intervalIntegrable_mul_continuous hlr.le hu (hflux.continuous_deriv (by simp))
    have hiNeg : IntervalIntegrable
        (fun x => -(u x * deriv (fun y => a y * deriv φ y) x)) volume l r := hi₁.neg
    have hi₂ : IntervalIntegrable (fun x => u x * (P x * φ x)) volume l r :=
      intervalIntegrable_mul_continuous hlr.le hu (hP.mul hφ.continuous)
    have hi₃ : IntervalIntegrable (fun x => F x * φ x) volume l r :=
      intervalIntegrable_mul_continuous hlr.le hF hφ.continuous
    have hleft : (∫ x in l..r, u x *
        (-deriv (fun y => a y * deriv φ y) x + P x * φ x)) =
        -(∫ x in l..r, u x * deriv (fun y => a y * deriv φ y) x) +
          ∫ x in l..r, u x * (P x * φ x) := by
      simp_rw [mul_add, mul_neg]
      rw [intervalIntegral.integral_add hiNeg hi₂, intervalIntegral.integral_neg]
    have hright : (∫ x in l..r, g x * φ x) =
        (∫ x in l..r, u x * (P x * φ x)) - ∫ x in l..r, F x * φ x := by
      have heq : (fun x => g x * φ x) =
          (fun x => u x * (P x * φ x) - F x * φ x) := by
        funext x
        dsimp only [g]
        ring
      rw [heq, intervalIntegral.integral_sub hi₂ hi₃]
    have htest := hweak φ hφ hφc hφs
    change (∫ x in l..r, u x *
      (-deriv (fun y => a y * deriv φ y) x + P x * φ x)) = _ at htest
    rw [hleft] at htest
    rw [hright]
    linarith only [htest]
  obtain ⟨v, huv, hv, hvdAC, hv₂, hvd₂, hvdd₂, hode, hfluxD⟩ :=
    n06_weak_divergence_L2_regular hlr ha han hu hg hdiv
  refine ⟨v, huv, hv, hvdAC, hv₂, hvd₂, hvdd₂, ?_, ?_⟩
  · filter_upwards [hfluxD, huv] with x hx hux
    dsimp only [g, P] at hx
    rw [hux] at hx
    nlinarith only [hx]
  · filter_upwards [hode, huv] with x hx hux
    dsimp only [g, P] at hx
    rw [hux] at hx
    nlinarith only [hx]

end ContinuousFlexibility.Analysis
