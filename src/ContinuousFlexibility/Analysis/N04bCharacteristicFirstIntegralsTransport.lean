module

public import ContinuousFlexibility.Analysis.N04bCharacteristicFirstIntegrals
public import ContinuousFlexibility.Analysis.RootPhysicalTransport

/-!
# Transport and reflection of the actual characteristic first integrals

Constancy of the actual inverse along the given forward trajectories gives
the minus transport equation. Reflection gives the plus first integral and
its transport equation when the drift is odd and the speed is even. The
normalizations at both physical endpoints are proved from the exact return
identity of the same forward flow.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual inverse first integral solves the characteristic PDE. -/
theorem n04b_minusFirstIntegral_transport
    {Φ d v : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL)
    (hflow : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun s => Φ (s, θ))
        (d (r, Φ (r, θ)) - v (r, Φ (r, θ))) r)
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) :
    radialPartial (n04bMinusFirstIntegral Φ hL) p =
      -(d p - v p) * angularPartial (n04bMinusFirstIntegral Φ hL) p := by
  let η := parameterizedCircleInverse Φ p
  have hη : Φ (p.1, η) = p.2 :=
    hΦ.inverse_right hP ⟨hp.1.1.le, hp.1.2.le⟩ p.2
  have hu : HasDerivAt (fun r => Φ (r, η)) (d p - v p) p.1 := by
    simpa only [hη] using hflow p.1 hp.1 η
  have hconstant : (fun r => n04bMinusFirstIntegral Φ hL (r, Φ (r, η)))
      =ᶠ[𝓝 p.1] (fun _ => hL η) := by
    filter_upwards [Icc_mem_nhds hp.1.1 hp.1.2] with r hr
    exact n04b_minusFirstIntegral_along_flow hΦ hL hr η
  have hd : DifferentiableAt ℝ (n04bMinusFirstIntegral Φ hL) p :=
    ((n04b_minusFirstIntegral_smooth hΦ hP hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  exact transport_of_constant_along_characteristic hd hu hη hconstant

/-- The other characteristic family is obtained by actual angular reflection. -/
def n04bPlusFirstIntegral (Φ : PolarPoint → ℝ) (hL : ℝ → ℝ) (p : PolarPoint) : ℝ :=
  -n04bMinusFirstIntegral Φ hL (p.1, -p.2)

/-- Actual partial derivatives under simultaneous reflection and negation. -/
theorem n04b_reflectedFirstIntegral_partials
    {V : PolarPoint → ℝ} {p : PolarPoint}
    (hV : DifferentiableAt ℝ V (p.1, -p.2)) :
    radialPartial (fun q : PolarPoint => -V (q.1, -q.2)) p =
        -radialPartial V (p.1, -p.2) ∧
      angularPartial (fun q : PolarPoint => -V (q.1, -q.2)) p =
        angularPartial V (p.1, -p.2) := by
  have hU : DifferentiableAt ℝ (fun q : PolarPoint => -V (q.1, -q.2)) p :=
    (hV.comp p (differentiableAt_fst.prodMk differentiableAt_snd.neg)).neg
  constructor
  · exact (hasDerivAt_radial_slice hU).unique (hasDerivAt_radial_slice hV).fun_neg
  · have hc := ((hasDerivAt_angular_slice hV).comp p.2 (hasDerivAt_neg p.2)).fun_neg
    have hs : HasDerivAt (fun θ => -V (p.1, -θ))
        (angularPartial V (p.1, -p.2)) p.2 := by
      simpa only [Function.comp_def, mul_neg_one, neg_neg] using hc
    exact (hasDerivAt_angular_slice hU).unique hs

theorem n04b_plusFirstIntegral_continuous
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : Continuous hL) :
    ContinuousOn (n04bPlusFirstIntegral Φ hL) (Icc a b ×ˢ univ) :=
  ((n04b_minusFirstIntegral_continuous hΦ hP hhL).comp
    (continuous_fst.prodMk continuous_snd.neg).continuousOn
    (fun p hp => ⟨hp.1, mem_univ _⟩)).neg

theorem n04b_plusFirstIntegral_smooth
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL) :
    ContDiffOn ℝ ∞ (n04bPlusFirstIntegral Φ hL) (Ioo a b ×ˢ univ) :=
  ((n04b_minusFirstIntegral_smooth hΦ hP hhL).comp
    (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn
    (fun p hp => ⟨hp.1, mem_univ _⟩)).neg

theorem n04b_plusFirstIntegral_angularPartial_pos
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL) (hLpos : ∀ θ, 0 < deriv hL θ)
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) :
    0 < angularPartial (n04bPlusFirstIntegral Φ hL) p := by
  have hp' : (p.1, -p.2) ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  have hd : DifferentiableAt ℝ (n04bMinusFirstIntegral Φ hL) (p.1, -p.2) :=
    ((n04b_minusFirstIntegral_smooth hΦ hP hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp')).differentiableAt (by simp)
  change 0 < angularPartial (fun q : PolarPoint =>
    -n04bMinusFirstIntegral Φ hL (q.1, -q.2)) p
  rw [(n04b_reflectedFirstIntegral_partials hd).2]
  exact n04b_minusFirstIntegral_angularPartial_pos hΦ hP hhL hLpos hp'

/-- Odd drift and even speed turn the reflected equation into the plus PDE. -/
theorem n04b_plusFirstIntegral_transport
    {Φ d v : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL)
    (hflow : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun s => Φ (s, θ))
        (d (r, Φ (r, θ)) - v (r, Φ (r, θ))) r)
    (hdodd : ∀ p ∈ Ioo a b ×ˢ univ, d (p.1, -p.2) = -d p)
    (hveven : ∀ p ∈ Ioo a b ×ˢ univ, v (p.1, -p.2) = v p)
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) :
    radialPartial (n04bPlusFirstIntegral Φ hL) p =
      -(d p + v p) * angularPartial (n04bPlusFirstIntegral Φ hL) p := by
  have hp' : (p.1, -p.2) ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  have hd : DifferentiableAt ℝ (n04bMinusFirstIntegral Φ hL) (p.1, -p.2) :=
    ((n04b_minusFirstIntegral_smooth hΦ hP hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp')).differentiableAt (by simp)
  have hpartials := n04b_reflectedFirstIntegral_partials hd
  have hminus := n04b_minusFirstIntegral_transport hΦ hP hhL hflow hp'
  unfold n04bPlusFirstIntegral
  rw [hpartials.1, hpartials.2, hminus, hdodd p hp, hveven p hp]
  ring

theorem n04b_plusFirstIntegral_period_add
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hLperiod : ∀ θ, hL (θ + P) = hL θ + P)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    n04bPlusFirstIntegral Φ hL (r, θ + P) =
      n04bPlusFirstIntegral Φ hL (r, θ) + P := by
  have h := n04b_minusFirstIntegral_period_add hΦ hP hLperiod hr (-(θ + P))
  have he : -(θ + P) + P = -θ := by ring
  rw [he] at h
  change -n04bMinusFirstIntegral Φ hL (r, -(θ + P)) =
    -n04bMinusFirstIntegral Φ hL (r, -θ) + P
  linarith

theorem n04b_plusFirstIntegral_left
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hab : a ≤ b)
    (hleft : ∀ θ, Φ (a, θ) = θ) (hLodd : ∀ θ, hL (-θ) = -hL θ) (θ : ℝ) :
    n04bPlusFirstIntegral Φ hL (a, θ) = hL θ := by
  change -n04bMinusFirstIntegral Φ hL (a, -θ) = hL θ
  rw [n04b_minusFirstIntegral_left hΦ hab hleft hL, hLodd, neg_neg]

theorem n04b_plusFirstIntegral_right
    {Φ : PolarPoint → ℝ} {hL hR : ℝ → ℝ} {a b P W : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0) (hab : a ≤ b)
    (hreturn : ∀ θ, hR (Φ (b, θ)) = hL θ - W)
    (hRodd : ∀ θ, hR (-θ) = -hR θ) (θ : ℝ) :
    n04bPlusFirstIntegral Φ hL (b, θ) = hR θ - W := by
  change -n04bMinusFirstIntegral Φ hL (b, -θ) = hR θ - W
  rw [n04b_minusFirstIntegral_right hΦ hP hab hreturn, hRodd]
  ring

end ContinuousFlexibility.Analysis
