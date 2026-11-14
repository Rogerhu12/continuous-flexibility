module

public import ContinuousFlexibility.Radial.ModeWeakGreen
public import ContinuousFlexibility.Radial.ModeRegionalPairing
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Closed-interval C2 regularity for homogeneous modal solutions

The C1 representative in the actual weak graph has an absolutely
continuous flux.  A continuous right-hand side makes this flux C1 up
to both regular cuts, and division by the positive physical profile
upgrades the representative to C2 on the closed interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Continuous principal source gives C2 regularity at both one-sided cuts. -/
theorem weakPrincipal_contDiffOn_two {a b : ℝ} (hab : a < b)
    {u g w : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hw : ContDiff ℝ ∞ w) (hwn : ∀ x ∈ Icc a b, w x ≠ 0)
    (hweak : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
        ∫ x in a..b, g x * ψ x) :
    ContDiffOn ℝ 2 u (Icc a b) := by
  have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab.le
  obtain ⟨hp, _, _⟩ := weakPrincipal_withinFlux_regular hab hu hgi hw hweak
  let p : ℝ → ℝ := fun x => w x * derivWithin u (Icc a b) x
  change ∀ x ∈ Icc a b, p x = p a + ∫ t in a..x, g t at hp
  have hpderiv (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt p (g x) (Icc a b) x := by
    letI : Fact (x ∈ Icc a b) := ⟨hx⟩
    have hix : IntervalIntegrable g volume a x :=
      (hg.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
    have hi := intervalIntegral.integral_hasDerivWithinAt_right
      (s := Icc a b) (t := Icc a b) hix
      (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hg x hx)
    exact (hi.const_add (p a)).congr (fun y hy => hp y hy) (hp x hx)
  have hpC : ContDiffOn ℝ 1 p (Icc a b) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr
    refine ⟨fun x hx => (hpderiv x hx).differentiableWithinAt, ?_⟩
    apply hg.congr
    intro x hx
    exact (hpderiv x hx).derivWithin ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt hx)
  have hdu : ContDiffOn ℝ 1 (derivWithin u (Icc a b)) (Icc a b) := by
    apply (hpC.div (hw.of_le (by simp)).contDiffOn hwn).congr
    intro x hx
    change derivWithin u (Icc a b) x =
      (w x * derivWithin u (Icc a b) x) / w x
    field_simp [hwn x hx]
  change ContDiffOn ℝ ((1 : ℕ∞ω) + 1) u (Icc a b)
  exact (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr
    ⟨hu.differentiableOn (by norm_num), by simp, hdu⟩

/-- The genuine homogeneous bordered modal equation upgrades any C1
representative to the C2 regularity demanded of the Poisson functions. -/
theorem modeLocalHomogeneous_contDiffOn_two {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {J : Set ℝ} {U : RadialModePair D}
    (hEq : ModeLocalEquation D j J U 0)
    {u : ℝ → ℝ} (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    {l h : ℝ} (hlh : l < h) (hsub : Icc l h ⊆ radialCore D)
    (hJ : Ioo l h ⊆ J) (hu : ContDiffOn ℝ 1 u (Icc l h)) :
    ContDiffOn ℝ 2 u (Icc l h) := by
  let g : ℝ → ℝ := fun r =>
    matchingPotential D j r * u r + U.2 * referenceColumn D r
  have hsub' : Icc l h ⊆ Icc D.a D.b := hsub.trans Ioo_subset_Icc_self
  have hg : ContinuousOn g (Icc l h) :=
    (((matchingPotential_continuousOn hD j).mono hsub').mul hu.continuousOn).add
      (continuousOn_const.mul ((matchingColumn_continuousOn hD hB).mono hsub'))
  apply weakPrincipal_contDiffOn_two hlh hu hg (matchingProfileGeometry hD).2.2.1.1
    (fun r hr => ((matchingProfileGeometry hD).2.2.2.2.1 r (hsub hr)).ne')
  intro ψ hψ hcψ hsupp
  rw [modeLocalEquation_representative_principal_on_compact hD hB hEq hrep
    hlh.le hsub hJ hψ hcψ hsupp]
  apply matchingSubinterval_congr_ae hD hlh.le hsub
  filter_upwards [hrep, (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D) :
    ⇑(0 : RadialModeL2 D) =ᵐ[radialHilbertMeasure D] 0)] with r hr hz
  dsimp only [matchingPrincipalSource, g, Prod.fst_zero]
  rw [hr, hz]
  simp only [Pi.zero_apply, mul_zero, sub_zero]

end ContinuousFlexibility.Radial
