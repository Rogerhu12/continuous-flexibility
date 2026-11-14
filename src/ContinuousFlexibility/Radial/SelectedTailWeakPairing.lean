module

public import ContinuousFlexibility.Radial.ModeWeakLinearity
public import ContinuousFlexibility.Analysis.L2RestrictionSplit

/-!
# Actual tail restriction, weak pairing and zero extension

The regional Hilbert space is the restriction of the same radial measure.
Its restriction and zero-extension maps are adjoint. Thus the full modal
weak identity follows from the proved regional pairing without changing
the frozen ordinary-support test class.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def RadialTailWeakPairing (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (right : Bool) (cut : ℝ) (j : ℕ)
    (R : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))) : Prop :=
  ∀ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ),
    Function.support ψ ⊆ radialTailInterval D right cut →
    ∀ f : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)),
      ⟪R f, l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)
        (matchingJacobiVector D hD j ψ hψ)⟫_ℝ =
      -⟪f, l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)
        (matchingSmoothVector D hD ψ hψ)⟫_ℝ

theorem outer_l2ZeroExtend_inner (μ : Measure ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (u : Lp ℝ 2 (μ.restrict s)) (g : Lp ℝ 2 μ) :
    ⟪l2ZeroExtend μ s hs u, g⟫_ℝ = ⟪u, l2Restrict μ s g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, ⟪l2ZeroExtend μ s hs u x, g x⟫_ℝ ∂μ) =
        ∫ x, s.indicator (fun x => u x * g x) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [l2ZeroExtend_coeFn μ s hs u] with x hx
      rw [hx, Real.inner_apply]
      by_cases hxs : x ∈ s
      · simp only [indicator_of_mem hxs]
      · simp only [indicator_of_notMem hxs, zero_mul]
    _ = ∫ x in s, u x * g x ∂μ := integral_indicator hs
    _ = ∫ x in s, ⟪u x, l2Restrict μ s g x⟫_ℝ ∂μ := by
      apply integral_congr_ae
      filter_upwards [l2Restrict_coeFn μ s g] with x hx
      rw [Real.inner_apply, hx]

theorem outer_l2ZeroExtend_restrict (μ : Measure ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (g : Lp ℝ 2 μ) (hgs : ∀ᵐ x ∂μ, x ∉ s → g x = 0) :
    l2ZeroExtend μ s hs (l2Restrict μ s g) = g := by
  apply Lp.ext
  filter_upwards [l2ZeroExtend_coeFn μ s hs (l2Restrict μ s g),
    ae_imp_of_ae_restrict (l2Restrict_coeFn μ s g), hgs] with x hx hr hz
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, hr hxs]
  · rw [indicator_of_notMem hxs, hz hxs]

def radialTailZeroExtendOperator (D : ReferenceData) (right : Bool) (cut : ℝ)
    (R : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))) :
    RadialModeL2 D →L[ℝ] RadialModeL2 D :=
  (l2ZeroExtend (radialHilbertMeasure D) (radialTailInterval D right cut)
    (by cases right <;> exact measurableSet_Ioo)).comp
      (R.comp (l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)))

theorem RadialTailWeakPairing.zeroExtend_equation
    {D : ReferenceData} {hD : IsAccumulatingProfile D} {right : Bool} {cut : ℝ} {j : ℕ}
    {R : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))}
    (hR : RadialTailWeakPairing D hD right cut j R) (F : RadialModePair D) :
    ModeLocalEquation D j (radialTailInterval D right cut)
      (radialTailZeroExtendOperator D right cut R F.1, 0) F := by
  let s := radialTailInterval D right cut
  have hs : MeasurableSet s := by cases right <;> exact measurableSet_Ioo
  apply (modeLocalEquation_iff_inner hD j s _ _).mpr
  intro ψ hψ _ hsψ
  have hg : (matchingSmoothVector D hD ψ hψ : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ψ :=
    MemLp.coeFn_toLp _
  have hz : ∀ᵐ x ∂radialHilbertMeasure D, x ∉ s → matchingSmoothVector D hD ψ hψ x = 0 := by
    filter_upwards [hg] with x hx hxs
    rw [hx]
    exact Function.notMem_support.mp (fun ht => hxs (hsψ ht))
  have hrestore := outer_l2ZeroExtend_restrict (radialHilbertMeasure D) hs
    (matchingSmoothVector D hD ψ hψ) hz
  have hsource := outer_l2ZeroExtend_inner (radialHilbertMeasure D) hs
    (l2Restrict (radialHilbertMeasure D) s (matchingSmoothVector D hD ψ hψ)) F.1
  rw [hrestore, real_inner_comm F.1 (matchingSmoothVector D hD ψ hψ),
    real_inner_comm (l2Restrict (radialHilbertMeasure D) s F.1)
      (l2Restrict (radialHilbertMeasure D) s (matchingSmoothVector D hD ψ hψ))] at hsource
  simp only [Prod.fst, Prod.snd, zero_mul, sub_zero]
  change ⟪l2ZeroExtend (radialHilbertMeasure D) s hs
    (R (l2Restrict (radialHilbertMeasure D) s F.1)), matchingJacobiVector D hD j ψ hψ⟫_ℝ = _
  rw [outer_l2ZeroExtend_inner, hR ψ hψ hsψ, ← hsource]

end ContinuousFlexibility.Radial
