import ContinuousFlexibility.Analysis.PrescribedEndpointWidth
import ContinuousFlexibility.Analysis.PositiveSymmetricFiberFactory

/-!
# Explicit angular collars separated from the middle interval

The displayed width depends only on the geometric margins and the
finite numerical input. The same width works before a family member
is chosen. The joint middle germ is the actual angular projection.
This file is reconstructed after the workspace reset.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

def endpointAngularWidth (n : ℕ) (l r c d κ M : ℝ) : ℝ :=
  prescribedEndpointWidth n (r - l) (min (c - l) (r - d)) κ M 0 1

theorem endpointAngularWidth_margins
    (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hM : 0 ≤ M) :
    let δ := endpointAngularWidth n l r c d κ M
    0 < δ ∧ δ ≤ 1 ∧ 2 * δ < r - l ∧
      δ < c - l ∧ δ < r - d ∧
      ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2 := by
  have hspan : 0 < r - l := sub_pos.mpr (hlc.trans (hcd.trans hdr))
  have hmargin : 0 < min (c - l) (r - d) :=
    lt_min (sub_pos.mpr hlc) (sub_pos.mpr hdr)
  obtain ⟨hδ, hmarginδ, hδone, hgap, hsmall, _⟩ :=
    prescribedEndpointWidth_margins n hspan hmargin hκ hM
      (show (0 : ℝ) ≤ 0 by rfl) zero_lt_one
  exact ⟨hδ, hδone, hgap,
    hmarginδ.trans_le (min_le_left _ _),
    hmarginδ.trans_le (min_le_right _ _), hsmall⟩

theorem endpointAngularInterpolation_family
    {ι : Type*} {n : ℕ} {A : ι → Bool → ℕ → ℝ → ℝ}
    {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hκone : κ ≤ 1) (hM : 0 ≤ M)
    (hA : ∀ i side j, j ≤ n → ContDiff ℝ ∞ (A i side j))
    (hzero : ∀ i side θ, κ ≤ deriv (A i side 0) θ)
    (hbound : ∀ i side j, 0 < j → j ≤ n → ∀ θ, |deriv (A i side j) θ| ≤ M)
    (hlift : ∀ i side θ, A i side 0 (θ + Real.pi) = A i side 0 θ + Real.pi)
    (hperiod : ∀ i side j, 0 < j → j ≤ n → Function.Periodic (A i side j) Real.pi)
    (hodd : ∀ i side j, j ≤ n → ∀ θ, A i side j (-θ) = -A i side j θ) :
    let δ := endpointAngularWidth n l r c d κ M
    0 < δ ∧ δ ≤ 1 ∧ 2 * δ < r - l ∧ δ < c - l ∧ δ < r - d ∧
      ∀ i, let φ := positiveAngularTaylorInterpolation n l r δ (A i)
      ContDiff ℝ ∞ φ ∧
      (∀ x θ, κ / 2 ≤ deriv (fun η => φ (x, η)) θ) ∧
      (∀ side k, k ≤ n → ∀ θ,
        radialBoundaryJet φ (if side then r else l) k θ = A i side k θ) ∧
      (∀ x θ, φ (x, θ + Real.pi) = φ (x, θ) + Real.pi) ∧
      (∀ x θ, φ (x, -θ) = -φ (x, θ)) ∧
      ∀ x ∈ Icc c d, ∀ θ, φ =ᶠ[𝓝 (x, θ)] (Prod.snd : PolarPoint → ℝ) := by
  obtain ⟨hδ, hδone, hgap, hδL, hδR, hsmall⟩ :=
    endpointAngularWidth_margins n hlc hcd hdr hκ hM
  dsimp only
  refine ⟨hδ, hδone, hgap, hδL, hδR, ?_⟩
  intro i
  refine ⟨contDiff_positiveAngularTaylorInterpolation (hA i) _ _ _,
    deriv_positiveAngularTaylorInterpolation_lower (hA i) hδ hδone hgap.le
      hκone hM (hzero i) (hbound i) hsmall,
    fun side k hk θ => iteratedDeriv_positiveAngularTaylorInterpolation n hδ hgap.le
      (A i) side hk θ,
    positiveAngularTaylorInterpolation_period_add (hlift i) (hperiod i) _ _ _,
    positiveAngularTaylorInterpolation_reflect (hodd i) _ _ _, ?_⟩
  intro x hx θ
  have hxL : x ∉ Metric.ball l (endpointAngularWidth n l r c d κ M) := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact not_lt.mpr (hδL.le.trans ((sub_le_sub_right hx.1 l).trans (le_abs_self _)))
  have hxR : x ∉ Metric.ball r (endpointAngularWidth n l r c d κ M) := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    exact not_lt.mpr (hδR.le.trans ((sub_le_sub_left hx.2 r).trans (le_abs_self _)))
  exact positiveAngularTaylorInterpolation_angle_germ n hδ (A i) hxL hxR θ

end ContinuousFlexibility.Analysis

