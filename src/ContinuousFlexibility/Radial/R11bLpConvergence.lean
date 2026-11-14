module

public import ContinuousFlexibility.Radial.R11bTensorL2
public import Mathlib.Analysis.Real.Sqrt

/-!
# Strong L² convergence and actual squared residuals

The equivalence uses the original measurable representatives. It holds for
an arbitrary measure and arbitrary filter, with no sigma-finiteness assumption.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open MeasureTheory Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem r11b_norm_toLp_sub_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  let u : Lp ℝ 2 μ := hf.toLp f - hg.toLp g
  have hn : ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
    simpa only [Lp.toLp_coeFn] using r11b_norm_toLp_sq (Lp.memLp u)
  calc
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := hn
    _ = ∫ x, (f x - g x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),
        hf.coeFn_toLp, hg.coeFn_toLp] with x hx hfx hgx
      change ((hf.toLp f - hg.toLp g) x) ^ 2 = (f x - g x) ^ 2
      rw [hx]
      change ((hf.toLp f) x - (hg.toLp g) x) ^ 2 = (f x - g x) ^ 2
      rw [hfx, hgx]

/-- Strong convergence of actual L² representatives is equivalent to
convergence of their squared residual integrals to zero. -/
theorem r11b_tendsto_toLp_iff_integral_sq_sub
    {ι α : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {f : ι → α → ℝ} {g : α → ℝ}
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : MemLp g 2 μ) :
    Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g)) ↔
      Tendsto (fun i => ∫ x, (f i x - g x) ^ 2 ∂μ) l (𝓝 0) := by
  have hsq (i : ι) :
      ‖(hf i).toLp (f i) - hg.toLp g‖ ^ 2 = ∫ x, (f i x - g x) ^ 2 ∂μ :=
    r11b_norm_toLp_sub_sq (hf i) hg
  constructor
  · intro h
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
    simpa only [hsq, zero_pow (by decide : 2 ≠ 0)] using hn.pow 2
  · intro h
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [← hsq, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h.sqrt

end

end ContinuousFlexibility.Radial
