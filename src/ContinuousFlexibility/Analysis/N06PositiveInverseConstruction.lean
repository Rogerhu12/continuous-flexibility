module

public import ContinuousFlexibility.Analysis.N06RadialPrimitiveConstruction

/-!
# The constructed positive reference map, inverse and physical primitive bounds

This closes the finite quantitative construction. The maps `Y` and `H`
are the original interpolation formulas with width `1 / (8 * A)`, and
`R0` is their actual inverse. Its smooth extension preserves every germ
on the closed unit interval. Ordinary endpoint and physical-profile jets
then give all primitive bounds with one fixed polynomial constant.

The physical profile bounds and the two-root lower bound are explicit
inputs. This theorem does not assert their uniform material dependence
for the accumulating family of actual roots.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Actual endpoint interpolation and actual inverse extension produce
the primitive package, from ordinary physical data rather than a proposed
bound for the resulting canonical coefficients. -/
theorem n06_positiveReference_regular_primitive_bounds :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ D : ReferenceData, ∀ l r A : ℝ,
      ∀ aL aR hL hR : ℝ → ℝ,
      RadialProfileGeometry D → 1 ≤ A →
      (1 / A ≤ r - l ∧ r - l ≤ A) → D.a < l → r < D.b →
      1 / A ≤ l → |l| ≤ A → |r| ≤ A →
      (∀ x ∈ Metric.ball l (n06PositiveReferenceWidth A), ContDiffAt ℝ ∞ aL x) →
      (∀ x ∈ Metric.ball r (n06PositiveReferenceWidth A), ContDiffAt ℝ ∞ aR x) →
      (∀ x ∈ Metric.ball l (n06PositiveReferenceWidth A), ContDiffAt ℝ ∞ hL x) →
      (∀ x ∈ Metric.ball r (n06PositiveReferenceWidth A), ContDiffAt ℝ ∞ hR x) →
      (∀ x ∈ Metric.ball l (n06PositiveReferenceWidth A),
        1 / A ≤ aL x ∧ N06ScalarJetTwoBound aL x A) →
      (∀ x ∈ Metric.ball r (n06PositiveReferenceWidth A),
        1 / A ≤ aR x ∧ N06ScalarJetTwoBound aR x A) →
      (∀ x ∈ Metric.ball l (n06PositiveReferenceWidth A),
        1 / A ≤ hL x ∧ N06ScalarJetTwoBound hL x A) →
      (∀ x ∈ Metric.ball r (n06PositiveReferenceWidth A),
        1 / A ≤ hR x ∧ N06ScalarJetTwoBound hR x A) →
      (∀ x ∈ Icc l r, 1 / A ≤ D.w x ∧
        N06ScalarJetTwoBound D.w x A ∧ N06ScalarJetTwoBound (deriv D.w) x A) →
      (∀ x ∈ Icc l r, (x - l) * (r - x) / A ≤ deriv D.w x / x) →
      (let δ : ℝ := n06PositiveReferenceWidth A
       let Y : ℝ → ℝ := positiveReferenceCoordinate l r δ aL aR
       let H : ℝ → ℝ := positiveReferenceHeight l r δ hL hR
       Function.Bijective Y ∧ ∃ R : ℝ → ℝ,
         N06RadialPrimitiveRegularity D.w H Y R ∧
           (∀ y ∈ Icc (0 : ℝ) 1, R =ᶠ[𝓝 y] Function.invFun Y) ∧
           ∀ y ∈ Icc (0 : ℝ) 1,
             N06RadialPrimitiveJetBounds D.w H Y R y (C0 * A ^ 336)) := by
  obtain ⟨C, hC, hforward⟩ := n06_positiveReference_forward_construction
  let C0 : ℝ := 4 * (2 * C) ^ 12
  have h2C : 1 ≤ 2 * C := by linarith
  have hpow : 1 ≤ (2 * C) ^ 12 := one_le_pow₀ h2C
  have hC0 : 1 ≤ C0 := by dsimp only [C0]; nlinarith
  refine ⟨C0, hC0, ?_⟩
  intro D l r A aL aR hL hR hD hA hwidth hlcore hrcore hlower hlabs hrabs
    hsL hsR hhL hhR hbL hbR hkL hkR hwjets hroot
  let δ : ℝ := n06PositiveReferenceWidth A
  let Y : ℝ → ℝ := positiveReferenceCoordinate l r δ aL aR
  let H : ℝ → ℝ := positiveReferenceHeight l r δ hL hR
  let R0 : ℝ → ℝ := Function.invFun Y
  obtain ⟨hY, hbij, hInvsm, hyL, hyR, hH, hYbounds, hHbounds, hjets⟩ :=
    hforward l r A aL aR hL hR hA hwidth hsL hsR hhL hhR hbL hbR hkL hkR
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hYpos : ∀ x, 0 < deriv Y x :=
    fun x => (one_div_pos.mpr (by positivity : 0 < 2 * A)).trans_le (hYbounds x).1
  have hYR : ∀ y, Y (R0 y) = y := Function.rightInverse_invFun hbij.2
  have hinside : ∀ y ∈ Icc (0 : ℝ) 1, R0 y ∈ Ioo D.a D.b := by
    intro y hy
    have hm := n06_inverse_mem_Icc (by positivity : 0 < 1 / (2 * A))
      (fun x => (hYbounds x).1) hYR hyL hyR hy
    exact ⟨hlcore.trans_le hm.1, hm.2.trans_lt hrcore⟩
  obtain ⟨R, hregular, hgerm, _⟩ :=
    n06_exists_regular_radialInverseExtension hD hH hY hInvsm hYpos hinside
  refine ⟨hbij, R, hregular, hgerm, ?_⟩
  intro y hy
  let B : ℝ := 2 * C * A ^ 28
  have hA28 : A ≤ A ^ 28 := by
    simpa only [pow_one] using pow_le_pow_right₀ hA (by norm_num : 1 ≤ 28)
  have hCA : A ≤ C * A ^ 28 :=
    hA28.trans (le_mul_of_one_le_left (pow_nonneg hAp.le _) hC)
  have hAB : 2 * A ≤ B := by
    dsimp only [B]
    nlinarith
  have hcap : C * A ^ 28 ≤ B := by
    dsimp only [B]
    nlinarith [mul_nonneg (zero_le_one.trans hC) (pow_nonneg hAp.le 28)]
  have hprimitive := n06_radialPrimitiveJetBounds_of_forward hw hH hY hbij hInvsm
    hA hAB hlower hlabs hrabs hyL hyR hYbounds (fun x => (hHbounds x).1)
    (fun x => (hjets x).1.mono hcap) (fun x => (hjets x).2.mono hcap)
    hwjets hroot hy
  have hfinal := hprimitive.congr_inverse (hgerm y hy)
  have hconstant : 4 * B ^ 12 = C0 * A ^ 336 := by
    dsimp only [B, C0]
    ring
  rw [hconstant] at hfinal
  exact hfinal

end ContinuousFlexibility.Analysis
