import ContinuousFlexibility.Analysis.WholePositiveAmbientRadialIdentity
import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields

/-!
# The full identity on an ambient side of the actual interpolation

Only the selected endpoint source is required to be identity/one. Its
actual Taylor data make its angular and height corrections vanish, while
the opposite cutoff is absent on this whole side of the middle interval.
Together with the actual radial integral this gives both inverse maps
and the height gauge, including genuine ordinary endpoint germs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveEndpointCutoff_opposite_zero_on_side
    {l r c d δ : ℝ} (hcd : c < d) (hδ : 0 < δ)
    (hL : δ ≤ c - l) (hR : δ ≤ r - d) (side : Bool)
    (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
    positiveEndpointCutoff (if side then l else r) δ p.1 = 0 := by
  apply positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ
  rw [Metric.mem_ball, Real.dist_eq]
  apply not_lt.mpr
  cases side with
  | false =>
      change p.1 ≤ c at hp
      change δ ≤ |p.1 - r|
      rw [abs_sub_comm]
      exact (hR.trans (sub_le_sub_left (hp.trans hcd.le) r)).trans (le_abs_self _)
  | true =>
      change d ≤ p.1 at hp
      change δ ≤ |p.1 - l|
      exact (hL.trans (sub_le_sub_right (hcd.le.trans hp) l)).trans (le_abs_self _)

theorem positiveAngularTaylorInterpolation_angle_on_identity_side
    (n : ℕ) {l r c d δ : ℝ} {A : Bool → ℕ → ℝ → ℝ}
    (hcd : c < d) (hδ : 0 < δ) (hL : δ ≤ c - l) (hR : δ ≤ r - d)
    (side : Bool)
    (hA : A side = radialBoundaryJet (Prod.snd : PolarPoint → ℝ)
      (if side then r else l))
    (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
    positiveAngularTaylorInterpolation n l r δ A p = p.2 := by
  have hzero := positiveEndpointCutoff_opposite_zero_on_side hcd hδ hL hR side p hp
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hA hzero
  <;> simp only [positiveAngularTaylorInterpolation, positiveAngularTaylorPatch,
    hA, boundaryTaylorPolynomial_snd, hzero, sub_self, mul_zero, zero_mul,
    add_zero, zero_add] <;> ring

theorem positiveHeightTaylorInterpolation_one_on_identity_side
    (n : ℕ) {l r c d δ : ℝ} {q : Bool → PolarPoint → ℝ}
    (hcd : c < d) (hδ : 0 < δ) (hL : δ ≤ c - l) (hR : δ ≤ r - d)
    (side : Bool)
    (hq : ∀ θ, q side =ᶠ[𝓝 (if side then r else l, θ)] (fun _ => (1 : ℝ)))
    (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
    positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q p = 1 := by
  have hdata : positiveHeightTaylorData l r (fun _ => 1) q side =
      (fun _ _ => (0 : ℝ)) := by
    funext k θ
    have hlog : ∀ η, boundaryHeightLogRatio (fun _ => 1) (q side) =ᶠ[
        𝓝 (if side then r else l, η)] (fun _ : PolarPoint => (0 : ℝ)) := by
      intro η
      filter_upwards [hq η] with x hx
      simp only [boundaryHeightLogRatio, hx, div_one, Real.log_one]
    simpa only [positiveHeightTaylorData, radialBoundaryJet,
      iteratedDeriv_fun_const_zero] using radialBoundaryJet_eq_of_joint_germ hlog k θ
  have hzero := positiveEndpointCutoff_opposite_zero_on_side hcd hδ hL hR side p hp
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hdata hzero
  <;> simp only [positiveHeightTaylorInterpolation, endpointTaylorCorrection,
    hdata, hzero, boundaryTaylorPolynomial, zero_div, zero_mul,
    Finset.sum_const_zero, mul_zero, zero_add, add_zero, Real.exp_zero, one_mul]

theorem oneSidedWholeComponentTransport_eq_on_identity_side
    (n : ℕ) {ψ X : Bool → PolarPoint → ℝ} {l r c d κφ κX M Mσ : ℝ}
    (hcd : c < d) (side : Bool)
    (hψ : ∀ θ, ψ side =ᶠ[𝓝 (if side then r else l, θ)]
      (Prod.snd : PolarPoint → ℝ))
    (hX : ∀ θ, X side =ᶠ[𝓝 (if side then r else l, θ)]
      (Prod.fst : PolarPoint → ℝ))
    (hδ : 0 < endpointAngularWidth (n + 1) l r c d κφ M)
    (hL : endpointAngularWidth (n + 1) l r c d κφ M ≤ c - l)
    (hR : endpointAngularWidth (n + 1) l r c d κφ M ≤ r - d)
    (hη : 0 < endpointFiberWidths n l r c d κX Mσ side)
    (hgap : 2 * endpointFiberWidths n l r c d κX Mσ side <
      (if side then r else c) - (if side then d else l))
    (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
    oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ p = p := by
  apply Prod.ext
  · exact oneSidedWholeComponentTransport_radial_eq_of_side_germ
      n hcd side hX hη hgap p hp
  · have hrep : oneSidedEndpointRepresentative (n + 2) l r ψ side =
        (Prod.snd : PolarPoint → ℝ) :=
      oneSidedBoundaryTaylorRepresentative_eq_snd hψ (n + 2)
    change positiveAngularTaylorInterpolation (n + 1) l r
      (endpointAngularWidth (n + 1) l r c d κφ M)
      (rawEndpointAngularData l r (oneSidedEndpointRepresentative (n + 2) l r ψ)) p = p.2
    apply positiveAngularTaylorInterpolation_angle_on_identity_side
      (n + 1) hcd hδ hL hR side _ p hp
    change radialBoundaryJet (oneSidedEndpointRepresentative (n + 2) l r ψ side)
      (if side then r else l) = _
    rw [hrep]

/-- The ordinary endpoint neighborhood stays on the selected side of the
middle. This is one Boolean endpoint argument, shared by all fields. -/
theorem eventually_mem_positive_endpoint_side
    {l r c d : ℝ} (hlc : l < c) (hdr : d < r) (side : Bool) (θ : ℝ) :
    ∀ᶠ p : PolarPoint in 𝓝 (if side then r else l, θ),
      if side then d ≤ p.1 else p.1 ≤ c := by
  cases side with
  | false =>
      have h : ∀ᶠ p : PolarPoint in 𝓝 (l, θ), p.1 < c :=
        (continuous_fst.tendsto (l, θ)).eventually (eventually_lt_nhds hlc)
      exact h.mono fun _ hp => hp.le
  | true =>
      have h : ∀ᶠ p : PolarPoint in 𝓝 (r, θ), d < p.1 :=
        (continuous_fst.tendsto (r, θ)).eventually (eventually_gt_nhds hdr)
      exact h.mono fun _ hp => hp.le

/-- These germs concern the actual inverse and gauge. No smoothness of
the physical coefficient field at an ambient endpoint is asserted. -/
theorem wholePositiveFields_identity_germs_of_side
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {l r c d : ℝ}
    (hlc : l < c) (hdr : d < r) (side : Bool)
    (hleft : Function.LeftInverse σ τ)
    (hτ : ∀ p : PolarPoint, (if side then d ≤ p.1 else p.1 ≤ c) → τ p = p)
    (hQ : ∀ p : PolarPoint, (if side then d ≤ p.1 else p.1 ≤ c) → Q p = 1)
    (θ : ℝ) :
    τ =ᶠ[𝓝 (if side then r else l, θ)] (id : PolarPoint → PolarPoint) ∧
      σ =ᶠ[𝓝 (if side then r else l, θ)] (id : PolarPoint → PolarPoint) ∧
      Q =ᶠ[𝓝 (if side then r else l, θ)] (fun _ => (1 : ℝ)) ∧
      wholePositiveChartHeight σ Q =ᶠ[𝓝 (if side then r else l, θ)]
        (fun _ => (1 : ℝ)) := by
  have hτg : τ =ᶠ[𝓝 (if side then r else l, θ)] (id : PolarPoint → PolarPoint) :=
    (eventually_mem_positive_endpoint_side hlc hdr side θ).mono fun p hp => hτ p hp
  have hσg : σ =ᶠ[𝓝 (if side then r else l, θ)] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hτg] with p hp
    exact (congrArg σ hp.symm).trans (hleft p)
  have hQg : Q =ᶠ[𝓝 (if side then r else l, θ)] (fun _ => (1 : ℝ)) :=
    (eventually_mem_positive_endpoint_side hlc hdr side θ).mono fun p hp => hQ p hp
  refine ⟨hτg, hσg, hQg, ?_⟩
  filter_upwards [hσg, hQg] with p hpσ hpQ
  simp only [wholePositiveChartHeight, hpσ, hpQ, inv_one]

end ContinuousFlexibility.Analysis
