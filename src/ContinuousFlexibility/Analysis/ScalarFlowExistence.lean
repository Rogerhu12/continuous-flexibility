import Mathlib.Analysis.ODE.ExistUnique

/-!
# Actual scalar flows on a prescribed bounded time interval

A globally bounded, uniformly Lipschitz scalar speed satisfies the
Picard--Lindelof hypotheses on a ball whose radius is the speed bound
times the length from the initial time. The resulting functions satisfy
the actual ODE and are continuous at both endpoints.

The family theorem makes the choices for every external parameter and
initial angle. It does not assume a parameterized flow as input, and it
does not assert parameter smoothness or high-order estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Metric
open scoped NNReal

/-- Global scalar speed bounds allow the actual solution to be constructed
on any prescribed closed time interval containing the initial time. -/
theorem exists_scalarFlow_on_Icc
    {F : ℝ → ℝ → ℝ} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {M K : ℝ≥0}
    (hLipschitz : ∀ t ∈ Icc a b, LipschitzWith K (F t))
    (hContinuous : ∀ θ, ContinuousOn (fun t => F t θ) (Icc a b))
    (hBound : ∀ t ∈ Icc a b, ∀ θ, ‖F t θ‖ ≤ (M : ℝ))
    (θ₀ : ℝ) :
    ∃ u : ℝ → ℝ, u t₀ = θ₀ ∧ ContinuousOn u (Icc a b) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt u (F t (u t)) (Icc a b) t) ∧
      (∀ t ∈ Ioo a b, HasDerivAt u (F t (u t)) t) := by
  let Δ : ℝ≥0 := NNReal.mk (max (b - t₀) (t₀ - a))
    ((sub_nonneg.mpr ht₀.2).trans (le_max_left _ _))
  have hPL : IsPicardLindelof F ⟨t₀, ht₀⟩ θ₀ (M * Δ) 0 M K := by
    refine ⟨fun t ht => (hLipschitz t ht).lipschitzOnWith,
      fun θ _ => hContinuous θ, fun t ht θ _ => hBound t ht θ, ?_⟩
    simp only [Δ, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_zero, sub_zero, le_refl]
  obtain ⟨u, hu, hdu⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨u, hu, fun t ht => (hdu t ht).continuousWithinAt, hdu, ?_⟩
  intro t ht
  exact (hdu t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Choose actual scalar flows simultaneously for every external parameter
and initial angle. Bounds may depend on the parameter; uniform quantitative
bounds and smooth dependence are separate conclusions to be proved later. -/
theorem exists_scalarFlowFamily_on_Icc
    {P : Type*} (F : P → ℝ → ℝ → ℝ)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (M K : P → ℝ≥0)
    (hLipschitz : ∀ p t, t ∈ Icc a b → LipschitzWith (K p) (F p t))
    (hContinuous : ∀ p θ, ContinuousOn (fun t => F p t θ) (Icc a b))
    (hBound : ∀ p t, t ∈ Icc a b → ∀ θ, ‖F p t θ‖ ≤ (M p : ℝ)) :
    ∃ Θ : P → ℝ → ℝ → ℝ, ∀ p θ,
      Θ p t₀ θ = θ ∧ ContinuousOn (fun t => Θ p t θ) (Icc a b) ∧
        (∀ t ∈ Icc a b,
          HasDerivWithinAt (fun s => Θ p s θ) (F p t (Θ p t θ)) (Icc a b) t) ∧
        (∀ t ∈ Ioo a b,
          HasDerivAt (fun s => Θ p s θ) (F p t (Θ p t θ)) t) := by
  have hex (p : P) (θ : ℝ) := exists_scalarFlow_on_Icc ht₀
    (hLipschitz p) (hContinuous p) (hBound p) θ
  choose u hu using hex
  exact ⟨fun p t θ => u p θ t, hu⟩

end ContinuousFlexibility.Analysis
