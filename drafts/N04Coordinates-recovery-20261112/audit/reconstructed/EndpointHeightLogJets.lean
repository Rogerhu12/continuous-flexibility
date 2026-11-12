import ContinuousFlexibility.Analysis.LogPolynomialEnvelope
import ContinuousFlexibility.Analysis.OneSidedEndpointHeight

/-!
# Finite logarithmic endpoint jets from actual positive height jets

The scalar logarithm envelope is evaluated at each genuine root point.
The one-sided smoothness identifies its radial trace with the ordinary
jet there; no smooth extension outside the physical strip is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem exists_oneSidedLogBoundaryJet_envelope (n : ℕ) :
    ∃ Clog : ℝ, 0 < Clog ∧ ∀ (H : ℝ), 1 ≤ H →
      ∀ (q : PolarPoint → ℝ) (a b c : ℝ), a < b →
      ContDiffOn ℝ ∞ q (Ioo a b ×ˢ (univ : Set ℝ)) → c ∈ Icc a b →
      (∀ θ, ContDiffAt ℝ ∞ q (c, θ)) →
      (∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), 0 < q p) →
      (∀ θ, 0 < q (c, θ)) →
      (∀ θ, q (c, θ) ≤ H) → (∀ θ, (q (c, θ))⁻¹ ≤ H) →
      (∀ k, 1 ≤ k → k ≤ n → ∀ θ,
        ‖iteratedFDeriv ℝ k q (c, θ)‖ ≤ H) →
      ∀ j, j ≤ n → ∀ θ,
        |radialBoundaryJet (fun p => Real.log (q p)) c j θ| ≤
          Clog * H ^ (2 * n + 1) := by
  obtain ⟨Clog, hClog, hbound⟩ :=
    exists_log_finiteJet_polynomial_envelope (E := PolarPoint) n
  refine ⟨Clog, lt_of_lt_of_le zero_lt_one hClog, ?_⟩
  intro H hH q a b c hab hq hc hqroot hpos hposroot hupper hinverse hjets j hj θ
  have hlog : ContDiffOn ℝ ∞ (fun p => Real.log (q p))
      (Ioo a b ×ˢ (univ : Set ℝ)) :=
    hq.log (fun p hp => (hpos p hp).ne')
  have hlogroot : ContDiffAt ℝ ∞ (fun p => Real.log (q p)) (c, θ) :=
    (hqroot θ).log (hposroot θ).ne'
  have hrad := abs_mixedDerivative_le_norm_iteratedFDeriv_on_closedStrip
    hab hlog (p := (c, θ)) hc hlogroot j 0
  have hrad' : |radialBoundaryJet (fun p => Real.log (q p)) c j θ| ≤
      ‖iteratedFDeriv ℝ j (fun p => Real.log (q p)) (c, θ)‖ := by
    simpa only [mixedDerivative, radialBoundaryJet, iteratedDeriv_zero, Nat.add_zero]
      using hrad
  exact hrad'.trans (hbound hH q (c, θ) (hqroot θ) (hposroot θ)
    (hupper θ) (hinverse θ) (fun k hk hkn => hjets k hk hkn θ) j hj)

end ContinuousFlexibility.Analysis

