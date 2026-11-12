import ContinuousFlexibility.Analysis.FiniteFirstJetInverse
import ContinuousFlexibility.Analysis.WholePositiveReferenceGauge

/-!
# Raw first jets after a fixed reference gauge

The displayed relative transports and heights retain their first jets
at one reference root point. Genuine inverse germs put both inverse
maps at that same point. Matching fixed reference fields then give the
raw current chart and height first jets at the actual current point.
The reference chart functions may already include the two fixed normal
translations and orientations; no state-dependent alignment is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem wholePositiveReferenceGauge_firstJets_of_transport
    {p : PolarPoint} {τ T σ S ψ Ψ : PolarPoint → PolarPoint}
    {h₀ g₀ Q q : PolarPoint → ℝ}
    (hτ : FiniteFullJetMatch 1 p τ T)
    (hσ : ContDiffAt ℝ ∞ σ (τ p)) (hS : ContDiffAt ℝ ∞ S (τ p))
    (hστ : σ ∘ τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hST : S ∘ T =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hTS : T ∘ S =ᶠ[𝓝 (τ p)] (id : PolarPoint → PolarPoint))
    (hψ : FiniteFullJetMatch 1 p ψ Ψ)
    (hh₀ : FiniteFullJetMatch 1 p h₀ g₀)
    (hQ : FiniteFullJetMatch 1 p Q q) (hQp : Q p ≠ 0) :
    FiniteFullJetMatch 1 (τ p)
        (wholePositiveReferenceGaugeChart ψ σ)
        (wholePositiveReferenceGaugeChart Ψ S) ∧
      FiniteFullJetMatch 1 (τ p)
        (wholePositiveReferenceGaugeHeight h₀ σ Q)
        (wholePositiveReferenceGaugeHeight g₀ S q) := by
  have hinv := finiteFullJetMatch_one_inverse_of_germs hτ hσ hS hστ hST hTS
  have hp : σ (τ p) = p := hστ.eq_of_nhds
  have hψat : FiniteFullJetMatch 1 (σ (τ p)) ψ Ψ := by
    rw [hp]
    exact hψ
  have hquot : FiniteFullJetMatch 1 (σ (τ p))
      (fun y => h₀ y / Q y) (fun y => g₀ y / q y) := by
    rw [hp]
    exact hh₀.div hQ hQp
  refine ⟨hinv.comp_match hψat, ?_⟩
  change FiniteFullJetMatch 1 (τ p)
    (fun x : PolarPoint => h₀ (σ x) * (Q (σ x))⁻¹)
    (fun x : PolarPoint => g₀ (S x) * (q (S x))⁻¹)
  simpa only [Function.comp_def, div_eq_mul_inv] using hinv.comp_match hquot

end ContinuousFlexibility.Analysis
