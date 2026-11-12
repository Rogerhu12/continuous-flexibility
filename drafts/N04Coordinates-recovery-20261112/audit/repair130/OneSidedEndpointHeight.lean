import ContinuousFlexibility.Analysis.OneSidedBoundaryTaylorRepresentative
import ContinuousFlexibility.Analysis.EndpointHeightValueBounds

/-!
# One common explicit collar for genuine one-sided height fields

The radius is the reciprocal of a displayed sum. Its inverse cost is
therefore exact, and its choice precedes the family index. Finite
ordinary jets match the actual one-sided field at both root circles.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def oneSidedEndpointHeightWidth (n : ℕ) (ρ M : ℝ) : ℝ :=
  (ρ⁻¹ + 1 + ((n + 1 : ℕ) : ℝ) * (M + 1))⁻¹

theorem oneSidedEndpointHeightWidth_margins (n : ℕ) {ρ M : ℝ}
    (hρ : 0 < ρ) (hM : 0 ≤ M) :
    let δ := oneSidedEndpointHeightWidth n ρ M
    0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
      δ⁻¹ = ρ⁻¹ + 1 + ((n + 1 : ℕ) : ℝ) * (M + 1) ∧
      ((n + 1 : ℕ) : ℝ) * M * δ ≤ 1 := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let D : ℝ := ρ⁻¹ + 1 + N * (M + 1)
  have hN : 0 < N := by
    change (0 : ℝ) < ((n + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_pos n
  have hρinv : 0 < ρ⁻¹ := inv_pos.mpr hρ
  have hprod : 0 ≤ N * (M + 1) := mul_nonneg hN.le (by linarith)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDρ : ρ⁻¹ ≤ D := by dsimp only [D]; linarith only [hprod]
  have hDone : 1 ≤ D := by dsimp only [D]; linarith only [hρinv, hprod]
  have hδρ : D⁻¹ ≤ ρ := by
    simpa only [inv_inv] using (inv_le_inv₀ hD hρinv).mpr hDρ
  have hδone : D⁻¹ ≤ 1 := by
    simpa only [inv_one] using (inv_le_inv₀ hD zero_lt_one).mpr hDone
  have hNM : N * M ≤ D := by dsimp only [D]; nlinarith only [hN, hρinv]
  have hsmall := mul_le_mul_of_nonneg_right hNM (inv_nonneg.mpr hD.le)
  rw [mul_inv_cancel₀ hD.ne'] at hsmall
  exact ⟨inv_pos.mpr hD, hδρ, hδone, inv_inv D, hsmall⟩

theorem exists_oneSidedEndpointHeight_family
    {ι : Type*} (n : ℕ) {h : ι → Bool → PolarPoint → ℝ}
    {a b : Bool → ℝ} {l r ρ M H : ℝ}
    (hab : ∀ side, a side < b side)
    (hend : ∀ side, (if side then r else l) ∈ Icc (a side) (b side))
    (hρ : 0 < ρ) (hρwidth : 2 * ρ ≤ r - l) (hM : 0 ≤ M) (hH : 1 ≤ H)
    (hregular : ∀ i side, ContDiffOn ℝ ∞ (h i side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hroot : ∀ i side θ, ContDiffAt ℝ ∞ (h i side) (if side then r else l, θ))
    (hpositive : ∀ i side θ, 0 < h i side (if side then r else l, θ))
    (hupper : ∀ i side θ, h i side (if side then r else l, θ) ≤ H)
    (hinverse : ∀ i side θ, (h i side (if side then r else l, θ))⁻¹ ≤ H)
    (hlog : ∀ i side j, 0 < j → j ≤ n → ∀ θ,
      |positiveHeightTaylorData l r (fun _ => 1) (h i) side j θ| ≤ M)
    (hperiod : ∀ i side, ∀ x ∈ Ioo (a side) (b side), ∀ θ,
      h i side (x, θ + Real.pi) = h i side (x, θ))
    (heven : ∀ i side, ∀ x ∈ Ioo (a side) (b side), ∀ θ,
      h i side (x, -θ) = h i side (x, θ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
      δ⁻¹ = ρ⁻¹ + 1 + ((n + 1 : ℕ) : ℝ) * (M + 1) ∧
      ∀ i,
      let Q := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h i)
      ContDiff ℝ ∞ Q ∧
      (∀ p, 0 < Q p) ∧
      (∀ side k, k ≤ n → ∀ θ,
        iteratedFDeriv ℝ k Q (if side then r else l, θ) =
          iteratedFDeriv ℝ k (h i side) (if side then r else l, θ)) ∧
      (∀ x θ, Q (x, θ + Real.pi) = Q (x, θ)) ∧
      (∀ x θ, Q (x, -θ) = Q (x, θ)) ∧
      (∀ p, p.1 ∉ Metric.ball l δ → p.1 ∉ Metric.ball r δ →
        Q =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) ∧
      ∀ p, Q p ≤ Real.exp 2 * H ^ 2 ∧ (Q p)⁻¹ ≤ Real.exp 2 * H ^ 2 := by
  let δ := oneSidedEndpointHeightWidth n ρ M
  obtain ⟨hδ, hδρ, hδone, hinv, hsmall⟩ :=
    oneSidedEndpointHeightWidth_margins n hρ hM
  have hgap : 2 * δ ≤ r - l := (mul_le_mul_of_nonneg_left hδρ (by norm_num)).trans hρwidth
  have hRef : ContDiff ℝ ∞ (fun _ : PolarPoint => (1 : ℝ)) := contDiff_const
  have hRefPos : ∀ _ : PolarPoint, (0 : ℝ) < 1 := fun _ => zero_lt_one
  refine ⟨δ, hδ, hδρ, hδone, hinv, ?_⟩
  intro i
  obtain ⟨hQ, hQpos⟩ := positiveHeightTaylorInterpolation_smooth_positive
    hRef hRefPos (hroot i) (hpositive i) n δ
  have hData (side : Bool) (τ : ℝ → ℝ) (hτ : ContDiff ℝ ∞ τ)
      (he : ∀ x ∈ Ioo (a side) (b side), ∀ θ, h i side (x, τ θ) = h i side (x, θ))
      (j : ℕ) (θ : ℝ) :
      positiveHeightTaylorData l r (fun _ => 1) (h i) side j (τ θ) =
        positiveHeightTaylorData l r (fun _ => 1) (h i) side j θ := by
    have hlogroot (η : ℝ) : ContDiffAt ℝ ∞
        (boundaryHeightLogRatio (fun _ => 1) (h i side))
        (if side then r else l, η) := by
      simpa only [boundaryHeightLogRatio, div_one] using
        (hroot i side η).log (hpositive i side η).ne'
    have heLog (x : ℝ) (hx : x ∈ Ioo (a side) (b side)) (η : ℝ) :
        boundaryHeightLogRatio (fun _ => 1) (h i side) (x, τ η) =
          0 + 1 * boundaryHeightLogRatio (fun _ => 1) (h i side) (x, η) := by
      simpa only [boundaryHeightLogRatio, div_one, zero_add, one_mul] using
        congrArg Real.log (he x hx η)
    simpa only [positiveHeightTaylorData, ite_self, zero_add, one_mul] using
      radialBoundaryJet_angleAffine_on_closedStrip
        (hab side) (hend side) hlogroot hτ heLog j θ
  refine ⟨hQ, hQpos, ?_, ?_, ?_,
    positiveHeightTaylorInterpolation_one_germ n hδ (h i),
    positiveHeightTaylorInterpolation_amplitude n hδ hδone hM hH
      (hpositive i) (hupper i) (hinverse i) (hlog i) hsmall⟩
  · intro side k hk θ
    exact iteratedFDeriv_eq_of_radialBoundaryJets_eq_on_closedStrip
      (hab side) hQ.contDiffOn (hregular i side) (hend side)
      (fun _ => hQ.contDiffAt) (hroot i side) (N := n)
      (fun j hj η => radialBoundaryJet_positiveHeightTaylorInterpolation
        hδ hgap hRef hRefPos (hroot i) (hpositive i) n side hj η) hk θ
  · exact positiveHeightTaylorInterpolation_angleInvariant (fun θ => θ + Real.pi)
      (fun _ _ => rfl)
      (fun side j _ => hData side (fun θ => θ + Real.pi)
        (contDiff_id.add contDiff_const) (hperiod i side) j)
  · exact positiveHeightTaylorInterpolation_angleInvariant (fun θ => -θ)
      (fun _ _ => rfl)
      (fun side j _ => hData side (fun θ => -θ) contDiff_neg (heven i side) j)

end ContinuousFlexibility.Analysis
