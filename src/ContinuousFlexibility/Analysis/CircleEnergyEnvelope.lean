module

public import ContinuousFlexibility.Analysis.CircleEnergyPointwiseBounds
public import ContinuousFlexibility.Analysis.MaterialComponentEnergy

/-!
# Circle realization from summable physical energy envelopes

The input of a return map can be a height, a circle field, or several
fields together. The weighted circle estimate only needs a summable
component energy envelope. This module keeps that envelope through the
infinite sum and gives both membership and the actual physical norm bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem circleEnergy_tsum_le_of_envelope
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ} {E : ℕ → ℝ≥0∞}
    (hE : (∑' m, E m) < ⊤) (hv : ∀ m, ContDiff ℝ ∞ (v m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (s : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hpoint : ∀ m b k, b + k ≤ s → ∀ θ,
      (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤ K * Real.sqrt (E m).toReal) :
    (∑' m, circleComponentEnergy T γ s v m) ≤
      ENNReal.ofReal ((Fintype.card (CircleJetIndex s) : ℝ) * (Real.pi * K ^ 2)) *
        ∑' m, E m := by
  have hterm (m : ℕ) : E m < ⊤ := (ENNReal.le_tsum m).trans_lt hE
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun m =>
    circleComponentEnergy_le_of_envelope hterm hv hM hH s hK hpoint m

theorem circleNorm_le_of_envelope
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ} {E : ℕ → ℝ≥0∞}
    (hE : (∑' m, E m) < ⊤) (hv : ∀ m, ContDiff ℝ ∞ (v m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (s : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hpoint : ∀ m b k, b + k ≤ s → ∀ θ,
      (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤ K * Real.sqrt (E m).toReal) :
    circleNorm T γ s v ≤
      Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) * (Real.pi * K ^ 2)) *
        Real.sqrt (∑' m, E m).toReal := by
  let A : ℝ := (Fintype.card (CircleJetIndex s) : ℝ) * (Real.pi * K ^ 2)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg Real.pi_pos.le (sq_nonneg _))
  have hbound := circleEnergy_tsum_le_of_envelope hE hv hM hH s hK hpoint
  have hfin : ENNReal.ofReal A * (∑' m, E m) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE).ne
  have hreal := ENNReal.toReal_mono hfin hbound
  change Real.sqrt (∑' m, circleComponentEnergy T γ s v m).toReal ≤
    Real.sqrt A * Real.sqrt (∑' m, E m).toReal
  calc
    _ ≤ Real.sqrt ((ENNReal.ofReal A * ∑' m, E m).toReal) := Real.sqrt_le_sqrt hreal
    _ = _ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, Real.sqrt_mul hA]

/-- An order-dependent summable envelope proves membership in the full
circle model. No global-seminorm bound is substituted for summability. -/
theorem circleMember_of_energy_envelope
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    (hv : ∀ m, ContDiff ℝ ∞ (v m) ∧ Function.Periodic (v m) Real.pi)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hpoint : ∀ s, ∃ E : ℕ → ℝ≥0∞, ∃ K : ℝ,
      (∑' m, E m) < ⊤ ∧ 0 ≤ K ∧
      ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
          |iteratedDeriv b (v m) θ| ≤ K * Real.sqrt (E m).toReal) :
    CircleMember T γ v := by
  refine ⟨hv, fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hv m).1 b, ?_⟩
  intro s
  obtain ⟨E, K, hE, hK, hpoint⟩ := hpoint s
  exact (circleEnergy_tsum_le_of_envelope hE (fun m => (hv m).1) hM hH s hK hpoint).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE)

/-- Disjoint actual radial components supply a summable envelope from
the full physical height energy. -/
theorem circleMember_of_physical_component_pointwise
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f : PolarPoint → ℝ} {v : ℕ → ℝ → ℝ} {l r : ℕ → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f)
    (hdisjoint : Pairwise (fun m n => Disjoint (Ioo (l m) (r m)) (Ioo (l n) (r n))))
    (hv : ∀ m, ContDiff ℝ ∞ (v m) ∧ Function.Periodic (v m) Real.pi)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hpoint : ∀ s, ∃ t : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
          |iteratedDeriv b (v m) θ| ≤
        K * Real.sqrt (physicalComponentEnergy T γ t f (l m) (r m)).toReal) :
    CircleMember T γ v := by
  apply circleMember_of_energy_envelope hv hM hH
  intro s
  obtain ⟨t, K, hK, hpoint⟩ := hpoint s
  exact ⟨fun m => physicalComponentEnergy T γ t f (l m) (r m), K,
    (physicalComponentEnergy_tsum_le hT hf hdisjoint t).trans_lt (physicalEnergy_lt_top hf t),
    hK, hpoint⟩

end ContinuousFlexibility.Statements
