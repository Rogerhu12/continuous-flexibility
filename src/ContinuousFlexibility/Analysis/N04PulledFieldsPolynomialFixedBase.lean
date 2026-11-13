import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseMixedProduct
import ContinuousFlexibility.Analysis.FlatMixedPolynomialCoefficients

/-!
# The actual correction polynomial preserves a common low base

Every monomial contains one independent residual velocity. Applying the
fixed-base mixed product and linear-combination rules therefore retains
its flat component factor and selects one low base before all parameter
orders. The supplied coefficient towers remain arbitrary genuine towers
of the same division-free polynomial.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

theorem n04PulledFields_polynomial_coefficient_fixedBaseGrowth
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p)
    (W F : I → ℝ) (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    {a b q ed ev rd rv outB outC : I → E × PolarPoint → ℝ}
    (Ja : ∀ i, SmoothDirections (U ×ˢ V i) (a i))
    (Jb : ∀ i, SmoothDirections (U ×ˢ V i) (b i))
    (Jq : ∀ i, SmoothDirections (U ×ˢ V i) (q i))
    (Jed : ∀ i, SmoothDirections (U ×ˢ V i) (ed i))
    (Jev : ∀ i, SmoothDirections (U ×ˢ V i) (ev i))
    (Jrd : ∀ i, SmoothDirections (U ×ˢ V i) (rd i))
    (Jrv : ∀ i, SmoothDirections (U ×ˢ V i) (rv i))
    (JB : ∀ i, SmoothDirections (U ×ˢ V i) (outB i))
    (JC : ∀ i, SmoothDirections (U ×ˢ V i) (outC i))
    (hB : ∀ i x, x ∈ U → ∀ y ∈ V i,
      outB i (x, y) = -a i (x, y) * rd i (x, y))
    (hC : ∀ i x, x ∈ U → ∀ y ∈ V i,
      outC i (x, y) =
        -2 * b i (x, y) * rd i (x, y) - a i (x, y) * ed i (x, y) * rd i (x, y) +
          2 * q i (x, y) * rv i (x, y) + a i (x, y) * ev i (x, y) * rv i (x, y))
    (ha : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Ja)
    (hb : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jb)
    (hq : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jq)
    (hed : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jed)
    (hev : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jev)
    (hrd : N04PulledFieldsFixedBaseMixedGrowth p W F Jrd)
    (hrv : N04PulledFieldsFixedBaseMixedGrowth p W F Jrv) :
    N04PulledFieldsFixedBaseMixedGrowth p W F JB ∧ N04PulledFieldsFixedBaseMixedGrowth p W F JC := by
  let Ta := fun i => (Ja i).mul (Jrd i)
  let T₀ := fun i => (Jb i).mul (Jrd i)
  let Tad := fun i => (Ja i).mul (Jed i)
  let Tav := fun i => (Ja i).mul (Jev i)
  let T₁ := fun i => (Tad i).mul (Jrd i)
  let T₂ := fun i => (Jq i).mul (Jrv i)
  let T₃ := fun i => (Tav i).mul (Jrv i)
  have hTa : N04PulledFieldsFixedBaseMixedGrowth p W F Ta := by
    simpa only [one_mul] using
      N04PulledFieldsFixedBaseMixedGrowth.mul hp hI hW (fun _ => zero_le_one) hF Ta
        hU hV hc (fun _ _ _ _ _ => rfl) ha hrd
  have hT₀ : N04PulledFieldsFixedBaseMixedGrowth p W F T₀ := by
    simpa only [one_mul] using
      N04PulledFieldsFixedBaseMixedGrowth.mul hp hI hW (fun _ => zero_le_one) hF T₀
        hU hV hc (fun _ _ _ _ _ => rfl) hb hrd
  have hTad : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Tad := by
    simpa only [one_mul] using
      N04PulledFieldsFixedBaseMixedGrowth.mul hp hI hW (fun _ => zero_le_one) (fun _ => zero_le_one)
        Tad hU hV hc (fun _ _ _ _ _ => rfl) ha hed
  have hTav : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Tav := by
    simpa only [one_mul] using
      N04PulledFieldsFixedBaseMixedGrowth.mul hp hI hW (fun _ => zero_le_one) (fun _ => zero_le_one)
        Tav hU hV hc (fun _ _ _ _ _ => rfl) ha hev
  have hT₁ : N04PulledFieldsFixedBaseMixedGrowth p W F T₁ := by
    simpa only [one_mul] using
      N04PulledFieldsFixedBaseMixedGrowth.mul hp hI hW (fun _ => zero_le_one) hF T₁
        hU hV hc (fun _ _ _ _ _ => rfl) hTad hrd
  have hT₂ : N04PulledFieldsFixedBaseMixedGrowth p W F T₂ := by
    simpa only [one_mul] using
      N04PulledFieldsFixedBaseMixedGrowth.mul hp hI hW (fun _ => zero_le_one) hF T₂
        hU hV hc (fun _ _ _ _ _ => rfl) hq hrv
  have hT₃ : N04PulledFieldsFixedBaseMixedGrowth p W F T₃ := by
    simpa only [one_mul] using
      N04PulledFieldsFixedBaseMixedGrowth.mul hp hI hW (fun _ => zero_le_one) hF T₃
        hU hV hc (fun _ _ _ _ _ => rfl) hTav hrv
  constructor
  · apply N04PulledFieldsFixedBaseMixedGrowth.linear_combination hp hW hF JB hV (-1) 0
      (hJ := hTa) (hK := hTa)
    intro i x hx y hy
    rw [hB i x hx y hy]
    ring
  · let T₀₁ := fun i => scalarLinearCombinationDirections (-2) (-1) (T₀ i) (T₁ i)
    let T₂₃ := fun i => scalarLinearCombinationDirections 2 1 (T₂ i) (T₃ i)
    have hT₀₁ : N04PulledFieldsFixedBaseMixedGrowth p W F T₀₁ :=
      N04PulledFieldsFixedBaseMixedGrowth.linear_combination hp hW hF T₀₁ hV (-2) (-1)
        (fun _ _ _ _ _ => rfl) hT₀ hT₁
    have hT₂₃ : N04PulledFieldsFixedBaseMixedGrowth p W F T₂₃ :=
      N04PulledFieldsFixedBaseMixedGrowth.linear_combination hp hW hF T₂₃ hV 2 1
        (fun _ _ _ _ _ => rfl) hT₂ hT₃
    apply N04PulledFieldsFixedBaseMixedGrowth.linear_combination hp hW hF JC hV 1 1
      (hJ := hT₀₁) (hK := hT₂₃)
    intro i x hx y hy
    rw [hC i x hx y hy]
    ring

end ContinuousFlexibility.Analysis
