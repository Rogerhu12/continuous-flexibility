import ContinuousFlexibility.Analysis.CircleEnergyEnvelope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A summable envelope for the difference of a scalar field curve

The real mean value theorem is applied after the fixed circle weight is
inserted. Thus the same summable envelope controls the two endpoint
fields without assuming that either endpoint already belongs to the
circle model.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

local instance circleCurveEnergyEnvelopeScalarNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set
open scoped Topology

theorem weighted_abs_sub_le_of_deriv_bound_unitInterval
    {F G : ℝ → ℝ} {w B : ℝ} (hw : 0 ≤ w)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (G t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, w * |G t| ≤ B) :
    w * |F 1 - F 0| ≤ B := by
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s => w * F s) (w * G t) (Icc (0 : ℝ) 1) t :=
    ((hderiv t ht).const_mul w).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖w * G t‖ ≤ B := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw] using hbound t ht
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01' hd
    (fun t ht => hb t ⟨ht.1, ht.2.le⟩)
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hw] at hm
  exact hm

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

local instance circleCurveEnergyEnvelopeRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

theorem circleMember_sub_of_curve_energy_envelope
    {T : MaterialData} {γ : ℝ}
    (F : ℝ → ℕ → ℝ → ℝ) (G : ℝ → ℕ → ℕ → ℝ → ℝ)
    (hF0 : ∀ m, ContDiff ℝ ∞ (F 0 m) ∧ Function.Periodic (F 0 m) Real.pi)
    (hF1 : ∀ m, ContDiff ℝ ∞ (F 1 m) ∧ Function.Periodic (F 1 m) Real.pi)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hderiv : ∀ m b θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun a => iteratedDeriv b (F a m) θ) (G t m b θ) t)
    (hbound : ∀ s, ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ,
      (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧ ∀ m b c, b + c ≤ s → ∀ θ t,
        t ∈ Icc (0 : ℝ) 1 →
        (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) * |G t m b θ| ≤
          K * Real.sqrt (E m).toReal) :
    CircleMember T γ (fun m θ => F 1 m θ - F 0 m θ) := by
  have hregular (m : ℕ) :
      ContDiff ℝ ∞ (fun θ => F 1 m θ - F 0 m θ) ∧
        Function.Periodic (fun θ => F 1 m θ - F 0 m θ) Real.pi := by
    constructor
    · exact (hF1 m).1.sub (hF0 m).1
    · intro θ
      dsimp only
      rw [(hF1 m).2 θ, (hF0 m).2 θ]
  apply circleMember_of_energy_envelope hregular hM hH
  intro s
  obtain ⟨E, K, hE, hK, hpoint⟩ := hbound s
  refine ⟨E, K, hE, hK, ?_⟩
  intro m b c hbc θ
  rw [iteratedDeriv_fun_sub ((hF1 m).1.contDiffAt.of_le (by simp))
    ((hF0 m).1.contDiffAt.of_le (by simp))]
  exact weighted_abs_sub_le_of_deriv_bound_unitInterval
    (mul_nonneg (pow_nonneg (hM m) c) (Real.rpow_nonneg (hH m) _))
    (hderiv m b θ) (hpoint m b c hbc θ)

end ContinuousFlexibility.Statements
