import ContinuousFlexibility.Analysis.LogPolynomialEnvelope
import ContinuousFlexibility.Analysis.OneSidedBoundaryJets
import ContinuousFlexibility.Analysis.PositiveHeightTaylorInterpolation

/-!
# Angular jets of the actual one-sided logarithmic Taylor data

The radial and angular orders add before the logarithm envelope is
selected. Commutation is obtained on the genuine open strip and then at
its closed edge through continuity of each finite derivative. No smooth
extension outside the physical strip is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem exists_oneSidedLogAngularJet_envelope (n N : ℕ) :
    ∃ Clog : ℝ, 1 ≤ Clog ∧ ∀ (H : ℝ), 1 ≤ H →
      ∀ (q : PolarPoint → ℝ) (a b c : ℝ), a < b →
      ContDiffOn ℝ ∞ q (Ioo a b ×ˢ (univ : Set ℝ)) → c ∈ Icc a b →
      (∀ θ, ContDiffAt ℝ ∞ q (c, θ)) →
      (∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), 0 < q p) →
      (∀ θ, 0 < q (c, θ)) →
      (∀ θ, q (c, θ) ≤ H) → (∀ θ, (q (c, θ))⁻¹ ≤ H) →
      (∀ k, 1 ≤ k → k ≤ n + N → ∀ θ,
        ‖iteratedFDeriv ℝ k q (c, θ)‖ ≤ H) →
      ∀ j, j ≤ n → ∀ k, k ≤ N → ∀ θ,
        |iteratedDeriv k (radialBoundaryJet (fun p => Real.log (q p)) c j) θ| ≤
          Clog * H ^ (2 * (n + N) + 1) := by
  obtain ⟨Clog, hClog, hbound⟩ :=
    exists_log_finiteJet_polynomial_envelope (E := PolarPoint) (n + N)
  refine ⟨Clog, hClog, ?_⟩
  intro H hH q a b c hab hq hc hqroot hpos hposroot hupper hinverse hjets j hj k hk θ
  have hlog : ContDiffOn ℝ ∞ (fun p => Real.log (q p))
      (Ioo a b ×ˢ (univ : Set ℝ)) :=
    hq.log (fun p hp => (hpos p hp).ne')
  have hlogroot : ∀ η, ContDiffAt ℝ ∞ (fun p => Real.log (q p)) (c, η) :=
    fun η => (hqroot η).log (hposroot η).ne'
  rw [iteratedDeriv_radialBoundaryJet_eq_mixedDerivative_on_closedStrip
    hab hlog hc hlogroot j k θ]
  exact (abs_mixedDerivative_le_norm_iteratedFDeriv_on_closedStrip
    hab hlog (p := (c, θ)) hc (hlogroot θ) j k).trans
      (hbound hH q (c, θ) (hqroot θ) (hposroot θ) (hupper θ) (hinverse θ)
        (fun s hs hsn => hjets s hs hsn θ) (j + k) (Nat.add_le_add hj hk))

/-- The coefficients supplied to the actual height interpolation satisfy
the full radial/angular rectangular bound. The same constant works for
every member of the family and is fixed before its numerical envelope. -/
theorem exists_oneSidedHeightTaylorData_angular_envelope {ι : Type*} (n N : ℕ) :
    ∃ Clog : ℝ, 1 ≤ Clog ∧ ∀ (H : ℝ), 1 ≤ H →
      ∀ (q : ι → Bool → PolarPoint → ℝ) (a b : Bool → ℝ) (l r : ℝ),
      (∀ side, a side < b side) →
      (∀ i side, ContDiffOn ℝ ∞ (q i side)
        (Ioo (a side) (b side) ×ˢ (univ : Set ℝ))) →
      (∀ side, (if side then r else l) ∈ Icc (a side) (b side)) →
      (∀ i side θ, ContDiffAt ℝ ∞ (q i side) (if side then r else l, θ)) →
      (∀ i side p ∈ Ioo (a side) (b side) ×ˢ (univ : Set ℝ), 0 < q i side p) →
      (∀ i side θ, 0 < q i side (if side then r else l, θ)) →
      (∀ i side θ, q i side (if side then r else l, θ) ≤ H) →
      (∀ i side θ, (q i side (if side then r else l, θ))⁻¹ ≤ H) →
      (∀ i side k, 1 ≤ k → k ≤ n + N → ∀ θ,
        ‖iteratedFDeriv ℝ k (q i side) (if side then r else l, θ)‖ ≤ H) →
      (∀ i side j, j ≤ n →
        ContDiff ℝ ∞ (positiveHeightTaylorData l r (fun _ => 1) (q i) side j)) ∧
      ∀ i side j, j ≤ n → ∀ k, k ≤ N → ∀ θ,
        |iteratedDeriv k (positiveHeightTaylorData l r (fun _ => 1) (q i) side j) θ| ≤
          Clog * H ^ (2 * (n + N) + 1) := by
  obtain ⟨Clog, hClog, hbound⟩ := exists_oneSidedLogAngularJet_envelope n N
  refine ⟨Clog, hClog, ?_⟩
  intro H hH q a b l r hab hq hend hqroot hpos hposroot hupper hinverse hjets
  have heq (i : ι) (side : Bool) :
      positiveHeightTaylorData l r (fun _ => 1) (q i) side =
        radialBoundaryJet (fun p => Real.log (q i side p)) (if side then r else l) := by
    simp only [positiveHeightTaylorData, boundaryHeightLogRatio, div_one]
  constructor
  · intro i side j _hj
    rw [heq i side]
    exact contDiff_radialBoundaryJet_of_contDiffAt (if side then r else l)
      (fun θ => (hqroot i side θ).log (hposroot i side θ).ne') j
  · intro i side j hj k hk θ
    rw [heq i side]
    exact hbound H hH (q i side) (a side) (b side) (if side then r else l)
      (hab side) (hq i side) (hend side) (hqroot i side) (hpos i side)
      (hposroot i side) (hupper i side) (hinverse i side) (hjets i side) j hj k hk θ

end ContinuousFlexibility.Analysis
