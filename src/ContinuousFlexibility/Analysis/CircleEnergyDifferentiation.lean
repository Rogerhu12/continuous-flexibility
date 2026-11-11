import ContinuousFlexibility.Analysis.CircleEnergyEnvelope
import ContinuousFlexibility.Analysis.CircleNonlinearRealization

/-!
# Genuine circle derivatives from summable remainder bounds

A componentwise Taylor estimate yields a derivative in the actual
projective topology when its energy envelope is summable. The error
factor tends to zero in every weighted order; the energy is kept inside
the component sum until the physical norm estimate is applied.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circle_tendsto_of_energy_envelope
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    {α : Type*} {l : Filter α} (u : α → S.Space) (v : S.Space)
    (hbound : ∀ s, ∃ E : ℕ → ℝ≥0∞, ∃ A : α → ℝ,
      (∑' m, E m) < ⊤ ∧ Tendsto A l (𝓝 0) ∧
      ∀ᶠ a in l, 0 ≤ A a ∧
        ∀ m b k, b + k ≤ s → ∀ θ,
          (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
            |iteratedDeriv b (S.decode (u a - v) m) θ| ≤
          A a * Real.sqrt (E m).toReal) :
    Tendsto u l (𝓝 v) := by
  have hiff := circle_tendsto_iff_norm hS (l := l) u v
  apply hiff.mpr
  intro s
  obtain ⟨E, A, hE, hA, hbound⟩ := hbound s
  have hlim : Tendsto
      (fun a : α =>
        Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) * (Real.pi * (A a) ^ 2)) *
          Real.sqrt (∑' m, E m).toReal) l (𝓝 0) := by
    have h := ((((hA.pow 2).const_mul Real.pi).const_mul
      (Fintype.card (CircleJetIndex s) : ℝ)).sqrt).mul_const
        (Real.sqrt (∑' m, E m).toReal)
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, Real.sqrt_zero, zero_mul] using h
  refine squeeze_zero' (Eventually.of_forall (fun _ => Real.sqrt_nonneg _)) ?_ hlim
  filter_upwards [hbound] with a ha
  exact circleNorm_le_of_envelope hE
    (fun m => ((hS.2.2.2.1 (u a - v)).1 m).1)
    hM hH s ha.1 ha.2

theorem circle_hasProjectiveCurveDerivAt_of_energy_envelope
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (c : ℝ → S.Space) (dc : S.Space) (t : ℝ)
    (hbound : ∀ s, ∃ E : ℕ → ℝ≥0∞, ∃ A : ℝ → ℝ,
      (∑' m, E m) < ⊤ ∧ Tendsto A (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧
      ∀ᶠ h in 𝓝[≠] (0 : ℝ), 0 ≤ A h ∧
        ∀ m b k, b + k ≤ s → ∀ θ,
          (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
            |iteratedDeriv b (S.decode (h⁻¹ • (c (t + h) - c t) - dc) m) θ| ≤
          A h * Real.sqrt (E m).toReal) :
    HasProjectiveCurveDerivAt c dc t :=
  circle_tendsto_of_energy_envelope hS hM hH
    (fun h : ℝ => h⁻¹ • (c (t + h) - c t)) dc hbound

/-- The affine-line version feeds the frozen N02 derivative clause
without reducing the target topology to pointwise evaluation. -/
theorem circle_hasProjectiveLineDerivAt_of_energy_envelope
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V → S.Space) (df : S.Space) (x v : V)
    (hbound : ∀ s, ∃ E : ℕ → ℝ≥0∞, ∃ A : ℝ → ℝ,
      (∑' m, E m) < ⊤ ∧ Tendsto A (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧
      ∀ᶠ h in 𝓝[≠] (0 : ℝ), 0 ≤ A h ∧
        ∀ m b k, b + k ≤ s → ∀ θ,
          (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
            |iteratedDeriv b (S.decode (h⁻¹ • (f (x + h • v) - f x) - df) m) θ| ≤
          A h * Real.sqrt (E m).toReal) :
    HasProjectiveLineDerivAt f df x v := by
  apply circle_hasProjectiveCurveDerivAt_of_energy_envelope hS hM hH
    (fun t : ℝ => f (x + t • v)) df 0
  simpa only [zero_add, zero_smul, add_zero] using hbound

end ContinuousFlexibility.Statements
