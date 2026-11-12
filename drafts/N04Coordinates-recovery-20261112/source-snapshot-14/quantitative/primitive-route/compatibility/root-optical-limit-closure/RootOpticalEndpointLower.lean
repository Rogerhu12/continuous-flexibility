import ContinuousFlexibility.Analysis.RootCharacteristicFactor
import Mathlib.Topology.Order.OrderClosed

/-!
# A root factor lower bound from the actual component optical inequality

The positive-side factorization is cancelled before taking a one-sided
limit. No common positive-width germ of all states is postulated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter Real Set
open scoped Topology ContDiff

theorem root_normalized_division_lower_at_zero
    {w g : ℝ → ℝ} {r σ ρ κ : ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    (hρ : 0 < ρ) (hr : 0 < r) (hwr : 0 < w r)
    (hfactor : ∀ t, -deriv w (r + σ * t) = t * g t)
    (hlower : ∀ t ∈ Ioo (0 : ℝ) ρ,
      κ * t ≤ -deriv w (r + σ * t) / ((r + σ * t) * w (r + σ * t))) :
    κ ≤ g 0 / (r * w r) := by
  let Q : ℝ → ℝ := fun t => g t / ((r + σ * t) * w (r + σ * t))
  have hshift : Continuous (fun t : ℝ => r + σ * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hQ : ContinuousAt Q 0 :=
    hg.continuous.continuousAt.div
      (hshift.continuousAt.mul (hw.continuous.comp hshift).continuousAt)
      (by simpa only [mul_zero, add_zero] using (mul_pos hr hwr).ne')
  have hcl : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) ρ) := by
    rw [closure_Ioo hρ.ne]
    exact ⟨le_rfl, hρ.le⟩
  haveI : NeBot (𝓝[Ioo (0 : ℝ) ρ] (0 : ℝ)) :=
    mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hb : ∀ᶠ t in 𝓝[Ioo (0 : ℝ) ρ] (0 : ℝ), κ ≤ Q t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := hlower t ht
    rw [hfactor] at h
    have he : (t * g t) / ((r + σ * t) * w (r + σ * t)) = t * Q t := by
      dsimp only [Q]
      ring
    rw [he, mul_comm κ t] at h
    exact (mul_le_mul_left ht.1).mp h
  have hlim := ge_of_tendsto hQ.continuousWithinAt.tendsto hb
  simpa only [Q, mul_zero, add_zero] using hlim

theorem referenceRootSpeedFactor_sq
    {w g : ℝ → ℝ} {r σ t : ℝ}
    (hr : 0 < r + σ * t) (hw : 0 < w (r + σ * t)) (hg : 0 < g t) :
    referenceRootSpeedFactor w g r σ t ^ 2 =
      g t / ((r + σ * t) * w (r + σ * t)) := by
  rw [referenceRootSpeedFactor, div_pow,
    Real.sq_sqrt (rootProfileRadicand_pos hr hw hg).le]
  dsimp only [rootProfileRadicand]
  field_simp [hr.ne', hw.ne'] <;> ring

/-- One orientation handles both actual endpoints of a negative component.
The returned quarter-factor is the lower factor used by N01's root input.
-/
theorem referenceRootSpeedFactor_lower_of_component_optical
    {w g : ℝ → ℝ} {l h κ : ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    (hl : 0 < l) (hlh : l < h) (hκ : 0 < κ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (rightEnd : Bool)
    (hfactor : ∀ t,
      -deriv w ((if rightEnd then h else l) + (if rightEnd then -1 else 1) * t) = t * g t)
    (hoptical : ∀ r ∈ Ioo l h,
      κ * min (r - l) (h - r) ≤ -deriv w r / (r * w r)) :
    let r := if rightEnd then h else l
    let σ : ℝ := if rightEnd then -1 else 1
    0 < referenceRootSpeedFactor w g r σ 0 ∧
      κ ≤ referenceRootSpeedFactor w g r σ 0 ^ 2 ∧
      (referenceRootSpeedFactor w g r σ 0 / 4)⁻¹ ≤ 4 * (1 + κ⁻¹) := by
  let r := if rightEnd then h else l
  let σ : ℝ := if rightEnd then -1 else 1
  have hrcc : r ∈ Icc l h := by
    cases rightEnd with
    | false => exact ⟨le_rfl, hlh.le⟩
    | true => exact ⟨hlh.le, le_rfl⟩
  have hr : 0 < r := hl.trans_le hrcc.1
  have hwr := hpos r hrcc
  have hρ : 0 < (h - l) / 2 := half_pos (sub_pos.mpr hlh)
  have hgeometry (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) ((h - l) / 2)) :
      r + σ * t ∈ Ioo l h ∧ min (r + σ * t - l) (h - (r + σ * t)) = t := by
    cases rightEnd with
    | false =>
      simp only [r, σ, Bool.false_eq_true, ↓reduceIte, one_mul]
      constructor
      · constructor <;> linarith only [ht.1, ht.2]
      · rw [min_eq_left (by linarith only [ht.2])]
        ring
    | true =>
      simp only [r, σ, ↓reduceIte, neg_one_mul]
      constructor
      · constructor <;> linarith only [ht.1, ht.2]
      · rw [min_eq_right (by linarith only [ht.2])]
        ring
  have hq : κ ≤ g 0 / (r * w r) :=
    root_normalized_division_lower_at_zero hw hg hρ hr hwr hfactor (fun t ht => by
      have hb := hoptical _ (hgeometry t ht).1
      simpa only [(hgeometry t ht).2] using hb)
  have hg0 : 0 < g 0 := by
    have he := (lt_div_iff₀ (mul_pos hr hwr)).mp (hκ.trans_le hq)
    simpa only [zero_mul] using he
  have hr0 : 0 < r + σ * 0 := by simpa only [mul_zero, add_zero] using hr
  have hw0 : 0 < w (r + σ * 0) := by simpa only [mul_zero, add_zero] using hwr
  have hv := referenceRootSpeedFactor_pos hr0 hw0 hg0
  have hs : κ ≤ referenceRootSpeedFactor w g r σ 0 ^ 2 := by
    rw [referenceRootSpeedFactor_sq hr0 hw0 hg0]
    simpa only [mul_zero, add_zero] using hq
  refine ⟨hv, hs, ?_⟩
  have hi : (referenceRootSpeedFactor w g r σ 0)⁻¹ ^ 2 ≤ κ⁻¹ := by
    rw [← inv_pow]
    exact inv_anti₀ hκ hs
  have hb : (referenceRootSpeedFactor w g r σ 0)⁻¹ ≤ 1 + κ⁻¹ := by
    nlinarith only [hi, sq_nonneg ((referenceRootSpeedFactor w g r σ 0)⁻¹ - (1 / 2 : ℝ))]
  rw [inv_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 4)

end ContinuousFlexibility.Analysis
