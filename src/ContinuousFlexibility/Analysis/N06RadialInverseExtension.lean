module

public import ContinuousFlexibility.Analysis.N06RadialPrimitiveBounds
public import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization

/-!
# A genuine global inverse extension for the radial reference formulas

The original inverse only has to map the closed unit interval into the
physical annulus. The existing smooth clamp gives a globally smooth
extension whose entire range lies in that annulus, while preserving the
original inverse on a neighborhood of every point of the closed interval.
Consequently all jets used by the material estimates are unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_inverse_unit_image_margin
    {R : ℝ → ℝ} {a b : ℝ} (hR : Continuous R)
    (hinside : ∀ y ∈ Icc (0 : ℝ) 1, R y ∈ Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Ioo (-δ) (1 + δ), R y ∈ Ioo a b := by
  have hopen : IsOpen (R ⁻¹' Ioo a b) := isOpen_Ioo.preimage hR
  obtain ⟨δ0, hδ0, h0⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds (hinside 0 ⟨le_rfl, zero_le_one⟩))
  obtain ⟨δ1, hδ1, h1⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds (hinside 1 ⟨zero_le_one, le_rfl⟩))
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1, fun y hy => ?_⟩
  by_cases hlo : y < 0
  · apply h0
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg hlo]
    linarith [min_le_left δ0 δ1, hy.1]
  by_cases hhi : 1 < y
  · apply h1
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hhi)]
    linarith [min_le_right δ0 δ1, hy.2]
  exact hinside y ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩

/-- The extension preserves germs even at the two endpoints. Its range
control is obtained by composition with the already constructed smooth
clamp, without choosing a new representation of a cutoff function. -/
theorem n06_exists_inverse_extension
    {R0 : ℝ → ℝ} {a b : ℝ} (hR0 : ContDiff ℝ ∞ R0)
    (hinside : ∀ y ∈ Icc (0 : ℝ) 1, R0 y ∈ Ioo a b) :
    ∃ R : ℝ → ℝ, ContDiff ℝ ∞ R ∧
      (∀ y, R y ∈ Ioo a b) ∧
      ∀ y ∈ Icc (0 : ℝ) 1, R =ᶠ[𝓝 y] R0 := by
  obtain ⟨δ, hδ, hmargin⟩ := n06_inverse_unit_image_margin hR0.continuous hinside
  have hab : -δ / 4 ≤ 1 + δ / 4 := by linarith
  have heps : 0 < δ / 4 := by positivity
  let κ : ℝ → ℝ :=
    circleFlowSmoothTimeClamp (-δ / 4) (1 + δ / 4) (δ / 4) hab heps
  let R : ℝ → ℝ := fun y => R0 (κ y)
  refine ⟨R, hR0.comp (contDiff_circleFlowSmoothTimeClamp hab heps), ?_, ?_⟩
  · intro y
    apply hmargin
    have hk : κ y ∈ Ioo (-δ / 4 - δ / 4) (1 + δ / 4 + δ / 4) :=
      circleFlowSmoothTimeClamp_mem hab heps y
    constructor <;> linarith [hk.1, hk.2]
  · intro y hy
    have hnear : Ioo (-δ / 4) (1 + δ / 4) ∈ 𝓝 y :=
      Ioo_mem_nhds (by linarith [hy.1]) (by linarith [hy.2])
    filter_upwards [hnear] with t ht
    change R0 (κ t) = R0 t
    have htκ : κ t = t :=
      circleFlowSmoothTimeClamp_eq hab heps ⟨ht.1.le, ht.2.le⟩
    rw [htκ]

/-- The actual positive reference profile supplies the global nonzero
denominators for the extended scalar formulas. Every original inverse jet
on the unit interval remains exactly the same, including endpoint jets. -/
theorem n06_exists_regular_radialInverseExtension
    {D : ReferenceData} (hD : RadialProfileGeometry D)
    {H Y R0 : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (hY : ContDiff ℝ ∞ Y) (hR0 : ContDiff ℝ ∞ R0)
    (hYpos : ∀ r, 0 < deriv Y r)
    (hinside : ∀ y ∈ Icc (0 : ℝ) 1, R0 y ∈ Ioo D.a D.b) :
    ∃ R : ℝ → ℝ, N06RadialPrimitiveRegularity D.w H Y R ∧
      (∀ y ∈ Icc (0 : ℝ) 1, R =ᶠ[𝓝 y] R0) ∧
      ∀ y ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, iteratedDeriv n R y = iteratedDeriv n R0 y := by
  obtain ⟨ha, _, hw, _, hwpos, _, _⟩ := hD
  obtain ⟨R, hR, hrange, heq⟩ := n06_exists_inverse_extension hR0 hinside
  refine ⟨R, ⟨hw.1, hH, hY, hR, ?_, ?_, ?_⟩, heq, ?_⟩
  · intro y
    exact (ha.trans (hrange y).1).ne'
  · intro y
    exact (hwpos (R y) (hrange y)).ne'
  · intro y
    exact (hYpos (R y)).ne'
  · intro y hy n
    exact Filter.EventuallyEq.iteratedDeriv_eq n (heq y hy)

end ContinuousFlexibility.Analysis
