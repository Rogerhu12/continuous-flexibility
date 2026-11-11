import ContinuousFlexibility.Analysis.AngularRegularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Radial integration preserves continuous angular derivatives

Continuity of the actual angular derivative on a compact rectangle supplies
the domination needed to differentiate the parameter integral.  This is
iterated without differentiating the radial variable.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem angular_parameter_integral_hasDerivAt
    {H : ℝ → ℝ → ℝ}
    (hH : Continuous (fun p : PolarPoint => H p.1 p.2))
    (hHd : ∀ r, Differentiable ℝ (H r))
    (hD : Continuous (fun p : PolarPoint => deriv (H p.1) p.2))
    (a b θ : ℝ) :
    HasDerivAt (fun x => ∫ s in a..b, H s x)
      (∫ s in a..b, deriv (H s) θ) θ := by
  have hK : IsCompact (uIcc a b ×ˢ Icc (θ - 1) (θ + 1)) :=
    isCompact_uIcc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
  have hHint : IntervalIntegrable (fun s => H s θ) volume a b :=
    (hH.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x s => H s x) (F' := fun x s => deriv (H s) x)
    (s := Ioo (θ - 1) (θ + 1)) (bound := fun _ => B)
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ hHint ?_ ?_
    intervalIntegrable_const ?_).2
  · exact Eventually.of_forall fun x =>
      (hH.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun s hs x hx =>
      hB (s, x) ⟨uIoc_subset_uIcc hs, ⟨hx.1.le, hx.2.le⟩⟩
  · exact Eventually.of_forall fun s _ x _ => (hHd s x).hasDerivAt

theorem continuous_angular_radial_primitive
    {H : ℝ → ℝ → ℝ} (hH : Continuous (fun p : PolarPoint => H p.1 p.2))
    (a : ℝ) : Continuous (fun p : PolarPoint => ∫ s in a..p.1, H s p.2) := by
  have hi : Continuous (fun p : PolarPoint × ℝ => H p.2 p.1.2) :=
    hH.comp (continuous_snd.prodMk continuous_fst.snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun p : PolarPoint => fun s => H s p.2)
    (by simpa only [Function.uncurry_def] using hi) continuous_fst

theorem AngularRegular.radial_primitive {n : ℕ} {H : ℝ → ℝ → ℝ}
    (hH : AngularRegular n H) (a : ℝ) :
    AngularRegular n (fun r θ => ∫ s in a..r, H s θ) := by
  induction n generalizing H with
  | zero => exact continuous_angular_radial_primitive hH.continuous a
  | succ n ih =>
    have hder (r θ : ℝ) := angular_parameter_integral_hasDerivAt
      hH.1 hH.2.1 hH.2.2.continuous a r θ
    refine ⟨continuous_angular_radial_primitive hH.1 a,
      fun r θ => (hder r θ).differentiableAt, ?_⟩
    exact (ih hH.2.2).congr fun r θ => (hder r θ).deriv

end ContinuousFlexibility.Analysis
