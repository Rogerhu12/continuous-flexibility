import ContinuousFlexibility.Radial.ZeroModePrimitive
import ContinuousFlexibility.Statements.Radial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Divergence of the actual endpoint resistance

A smooth profile vanishing at the right endpoint is bounded above there
by a constant times the distance to that endpoint. Positivity in the core
then forces its resistance primitive to diverge at least logarithmically.
Only the actual profile geometry is used.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false in
theorem zeroMode_resistance_tendsto_atTop
    {D : ReferenceData} (hD : RadialProfileGeometry D)
    {c : ℝ} (hc : c ∈ radialCore D) :
    Tendsto (fun r => ∫ s in c..r, (D.w s)⁻¹) (𝓝[<] D.b) atTop := by
  rcases hD with ⟨_, _, ⟨hw, hwout⟩, _, hwpos, _, _⟩
  have hwb : D.w D.b = 0 := hwout D.b (Or.inr le_rfl)
  obtain ⟨L₀, hLip⟩ :=
    (hw.contDiffOn : ContDiffOn ℝ ∞ D.w (Icc c D.b)).exists_lipschitzOnWith
      (by simp) (convex_Icc c D.b) isCompact_Icc
  let L : ℝ := (L₀ : ℝ) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hbound (s : ℝ) (hs : s ∈ Icc c D.b) : D.w s ≤ L * (D.b - s) := by
    have hh := hLip.dist_le_mul s hs D.b ⟨hc.2.le, le_rfl⟩
    have hh' : |D.w s| ≤ (L₀ : ℝ) * (D.b - s) := by
      simpa only [Real.dist_eq, hwb, sub_zero,
        abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub] using hh
    calc
      D.w s ≤ |D.w s| := le_abs_self _
      _ ≤ (L₀ : ℝ) * (D.b - s) := hh'
      _ ≤ L * (D.b - s) :=
        mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (sub_nonneg.mpr hs.2)
  have hlower (r : ℝ) (hr : r ∈ Ioo c D.b) :
      (log (D.b - c) - log (D.b - r)) / L ≤
        ∫ s in c..r, (D.w s)⁻¹ := by
    have hcore (s : ℝ) (hs : s ∈ Icc c r) : s ∈ radialCore D :=
      ⟨hc.1.trans_le hs.1, hs.2.trans_lt hr.2⟩
    have hden : ContinuousOn (fun s => (D.b - s)⁻¹) (Icc c r) :=
      (continuous_const.sub continuous_id).continuousOn.inv₀
        (fun s hs => (sub_pos.mpr (hs.2.trans_lt hr.2)).ne')
    have hi : IntervalIntegrable (fun s => (D.b - s)⁻¹) volume c r :=
      hden.intervalIntegrable_of_Icc hr.1.le
    have hwi : IntervalIntegrable (fun s => (D.w s)⁻¹) volume c r :=
      (hw.continuous.continuousOn.inv₀
        (fun s hs => (hwpos s (hcore s hs)).ne')).intervalIntegrable_of_Icc hr.1.le
    have hlogint :
        (∫ s in c..r, (D.b - s)⁻¹) = log (D.b - c) - log (D.b - r) := by
      have hd (s : ℝ) (hs : s ∈ uIcc c r) :
          HasDerivAt (fun t => -log (D.b - t)) ((D.b - s)⁻¹) s := by
        rw [uIcc_of_le hr.1.le] at hs
        have hne : D.b - s ≠ 0 := (sub_pos.mpr (hs.2.trans_lt hr.2)).ne'
        simpa only [id_eq, neg_div, neg_neg, one_div] using
          (((hasDerivAt_id s).const_sub D.b).log hne).fun_neg
      calc
        (∫ s in c..r, (D.b - s)⁻¹) =
            -log (D.b - r) - -log (D.b - c) :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
        _ = _ := by ring
    have hmono := intervalIntegral.integral_mono_on hr.1.le
      (hi.const_mul L⁻¹) hwi (fun s hs => by
        have hs' : s ∈ Icc c D.b := ⟨hs.1, hs.2.trans hr.2.le⟩
        have hh := one_div_le_one_div_of_le (hwpos s (hcore s hs)) (hbound s hs')
        simpa only [one_div, mul_inv] using hh)
    rw [intervalIntegral.integral_const_mul, hlogint] at hmono
    simpa only [div_eq_mul_inv, mul_comm] using hmono
  have hcont : ContinuousAt (fun r : ℝ => D.b - r) D.b :=
    (continuous_const.sub continuous_id).continuousAt
  have hzero : Tendsto (fun r : ℝ => D.b - r) (𝓝[<] D.b) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : Tendsto (fun r : ℝ => D.b - r) (𝓝[<] D.b) (𝓟 (Ioi (0 : ℝ))) := by
    apply tendsto_principal.mpr
    filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact sub_pos.mpr (show r < D.b from hr)
  have hright : Tendsto (fun r : ℝ => D.b - r) (𝓝[<] D.b) (𝓝[>] (0 : ℝ)) := by
    simpa only [inf_idem] using hzero.inf hpos
  have hlog : Tendsto (fun r : ℝ => log (D.b - r)) (𝓝[<] D.b) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hright
  apply tendsto_atTop.mpr
  intro A
  have hsmall := hlog.eventually (eventually_le_atBot (log (D.b - c) - L * A))
  filter_upwards [hsmall, Ioo_mem_nhdsLT hc.2] with r hr hri
  exact ((le_div_iff₀ hL).mpr (by nlinarith only [hr])).trans (hlower r hri)

end ContinuousFlexibility.Radial
