module

public import ContinuousFlexibility.Radial.OuterGreenIntegral
public import ContinuousFlexibility.Analysis.L2KernelRepresentation
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Symmetry of the actual all-source Green operator

Fubini is used first for two smooth compact interior tests, where the
double integrand has compact support and is integrable. Density and the
bounded operator then extend the identity to all of weighted L².
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Analysis

private theorem selected_green_continuousOn {a b lam : ℝ} {U V : ℝ → ℝ}
    (hU : ContinuousOn U (Ioo a b)) (hV : ContinuousOn V (Ioo a b)) :
    ContinuousOn (fun z : ℝ × ℝ => outerGreenKernel lam U V z.1 z.2)
      (Ioo a b ×ˢ Ioo a b) := by
  have hmin : MapsTo (fun z : ℝ × ℝ => min z.1 z.2)
      (Ioo a b ×ˢ Ioo a b) (Ioo a b) := by
    intro z hz
    exact ⟨lt_min hz.1.1 hz.2.1, (min_le_left _ _).trans_lt hz.1.2⟩
  have hmax : MapsTo (fun z : ℝ × ℝ => max z.1 z.2)
      (Ioo a b ×ˢ Ioo a b) (Ioo a b) := by
    intro z hz
    exact ⟨hz.1.1.trans_le (le_max_left _ _), max_lt hz.1.2 hz.2.2⟩
  exact continuousOn_const.mul
    ((hU.comp (continuous_fst.min continuous_snd).continuousOn hmin).mul
      (hV.comp (continuous_fst.max continuous_snd).continuousOn hmax))

theorem outerGreenOperator_isSymmetric (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b lam : ℝ} {U V : ℝ → ℝ}
    (hfull : ∀ᵐ x ∂μ, x ∈ Ioo a b)
    (hU : ContinuousOn U (Ioo a b)) (hV : ContinuousOn V (Ioo a b))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ] fun x =>
      ∫ y, outerGreenKernel lam U V x y * f y ∂μ) :
    R.toLinearMap.IsSymmetric := by
  let S := l2SmoothTestSubmodule μ (Ioo a b)
  have hS : Dense (S : Set (Lp ℝ 2 μ)) := dense_l2SmoothTestSubmodule isOpen_Ioo hfull
  have htest : ∀ f ∈ S, ∀ g ∈ S, ⟪R f, g⟫_ℝ = ⟪f, R g⟫_ℝ := by
    rintro f ⟨φ, hφ, hcφ, hsφ, hf⟩ g ⟨ψ, hψ, hcψ, hsψ, hg⟩
    let B : ℝ → ℝ → ℝ := fun x y => outerGreenKernel lam U V x y * φ y * ψ x
    have hsupport : Function.support (Function.uncurry B) ⊆ tsupport ψ ×ˢ tsupport φ := by
      intro z hz
      constructor
      · by_contra hx
        apply hz
        change outerGreenKernel lam U V z.1 z.2 * φ z.2 * ψ z.1 = 0
        rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
      · by_contra hy
        apply hz
        change outerGreenKernel lam U V z.1 z.2 * φ z.2 * ψ z.1 = 0
        rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, zero_mul]
    have hcont : ContinuousOn (Function.uncurry B) (tsupport ψ ×ˢ tsupport φ) :=
      (((selected_green_continuousOn hU hV).mono
        (fun z hz => ⟨hsψ hz.1, hsφ hz.2⟩)).mul
          (hφ.continuous.comp continuous_snd).continuousOn).mul
            (hψ.continuous.comp continuous_fst).continuousOn
    have hi : Integrable (Function.uncurry B) (μ.prod μ) :=
      (integrableOn_iff_integrable_of_support_subset hsupport).mp
        (hcont.integrableOn_compact (hcψ.prod hcφ))
    have hl : ⟪R f, g⟫_ℝ = ∫ x, ∫ y, B x y ∂μ ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hR f, hg] with x hx hgx
      rw [Real.inner_apply, hx, hgx, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [hf] with y hy
      dsimp only [B]
      rw [hy]
    have hr : ⟪f, R g⟫_ℝ = ∫ y, ∫ x, B x y ∂μ ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hR g, hf] with y hy hfy
      rw [Real.inner_apply, hy, hfy, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      dsimp only [B]
      rw [hx, outerGreenKernel_symm lam U V y x]
      ring
    exact hl.trans ((integral_integral_swap hi).trans hr.symm)
  have hright : ∀ f ∈ S, ∀ g : Lp ℝ 2 μ, ⟪R f, g⟫_ℝ = ⟪f, R g⟫_ℝ := by
    intro f hf
    have he : EqOn (fun g : Lp ℝ 2 μ => ⟪R f, g⟫_ℝ)
        (fun g => ⟪f, R g⟫_ℝ) S := fun g hg => htest f hf g hg
    have hfun := Continuous.ext_on hS
      (continuous_const.inner continuous_id) (continuous_const.inner R.continuous) he
    exact fun g => congrFun hfun g
  intro f g
  have he : EqOn (fun f : Lp ℝ 2 μ => ⟪R f, g⟫_ℝ)
      (fun f => ⟪f, R g⟫_ℝ) S := fun f hf => hright f hf g
  exact congrFun (Continuous.ext_on hS
    (R.continuous.inner continuous_const) (continuous_id.inner continuous_const) he) f

end ContinuousFlexibility.Radial
