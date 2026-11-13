import ContinuousFlexibility.Analysis.N04NegativeInverseForwardBounds

/-!
# Preserve the parameter height while changing retained samples

The two retained halves of one component have bounded endpoint distance.
The zero and positive parameter orders use the existing sample transfer
with height exponents zero and three quarters. A common coefficient and
exponent package both cases without changing that height exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

private theorem n04NegativeInverse_pair_weight_scalar
    {C E Es H Hs B₀ B₁ A₀ A₁ : ℝ}
    (hC : 0 ≤ C) (hE : 1 ≤ E) (hH : 0 ≤ H)
    (hB₀ : 0 ≤ B₀)
    (hzero : Es ^ C ≤ B₀ * E ^ A₀)
    (hpositive : Hs * Es ^ C ≤ B₁ * (H * E ^ A₁)) (κ : ℕ) :
    C * Es ^ C * parameterHeightWeight Hs κ ≤
      (C * max B₀ B₁) * E ^ (max A₀ A₁) * parameterHeightWeight H κ := by
  have hmax : 0 ≤ max B₀ B₁ := hB₀.trans (le_max_left _ _)
  have hb₀ : B₀ * E ^ A₀ ≤ max B₀ B₁ * E ^ (max A₀ A₁) :=
    mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) hmax
  have hb₁ : B₁ * E ^ A₁ ≤ max B₀ B₁ * E ^ (max A₀ A₁) :=
    mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) hmax
  by_cases hκ : κ = 0
  · subst κ
    simp only [parameterHeightWeight, if_pos rfl, mul_one]
    exact (mul_le_mul_of_nonneg_left (hzero.trans hb₀) hC).trans_eq (by ring)
  · have hp : Hs * Es ^ C ≤ (max B₀ B₁ * E ^ (max A₀ A₁)) * H := by
      calc
        _ ≤ B₁ * (H * E ^ A₁) := hpositive
        _ = (B₁ * E ^ A₁) * H := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hb₁ hH
    simp only [parameterHeightWeight, if_neg hκ]
    calc
      C * Es ^ C * Hs = C * (Hs * Es ^ C) := by ring
      _ ≤ C * ((max B₀ B₁ * E ^ (max A₀ A₁)) * H) :=
        mul_le_mul_of_nonneg_left hp hC
      _ = _ := by ring

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Transfer a complete current-jet envelope from `k'` to `k` in the
same original component. The constant is uniform in the parameter arity,
and every positive order keeps exactly the original height exponent. -/
theorem negativeInverse_pair_sample_heightWeight (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space) k k' m side side',
        G.e k = .inl (m, side) → G.e k' = .inl (m, side') → ∀ κ : ℕ,
          C * G.W.U.E0 (G.W.U.sample ((G.V η).cell k')) ^ C *
              parameterHeightWeight
                (G.W.U.H (G.W.U.sample ((G.V η).cell k')) ^ (3 / 4 : ℝ)) κ ≤
            B * G.W.U.E0 (G.W.U.sample ((G.V η).cell k)) ^ B *
              parameterHeightWeight
                (G.W.U.H (G.W.U.sample ((G.V η).cell k)) ^ (3 / 4 : ℝ)) κ := by
  obtain ⟨B₀, A₀, hB₀, _hA₀, hb₀⟩ := G.negativeInverse_pair_sample_weights 0 C hC
  obtain ⟨B₁, A₁, _hB₁, _hA₁, hb₁⟩ :=
    G.negativeInverse_pair_sample_weights (3 / 4 : ℝ) C hC
  obtain ⟨b, _hb, hpack⟩ := coefficientEnvelope_pack (C * max B₀ B₁) (max A₀ A₁)
  let B : ℝ := max b 1
  have hB : 1 ≤ B := le_max_right _ _
  have hbB : b ≤ B := le_max_left _ _
  refine ⟨B, hB, ?_⟩
  intro η k k' m side side' hk hk' κ
  let E : ℝ := G.W.U.E0 (G.W.U.sample ((G.V η).cell k))
  let Es : ℝ := G.W.U.E0 (G.W.U.sample ((G.V η).cell k'))
  let H : ℝ := G.W.U.H (G.W.U.sample ((G.V η).cell k)) ^ (3 / 4 : ℝ)
  let Hs : ℝ := G.W.U.H (G.W.U.sample ((G.V η).cell k')) ^ (3 / 4 : ℝ)
  have hE : 1 ≤ E := (G.cost_nonneg η).2.2 k
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg η).2.1 k) _
  have hzero : Es ^ C ≤ B₀ * E ^ A₀ := by
    simpa only [Real.rpow_zero, one_mul] using hb₀ η k k' m side side' hk hk'
  have hpositive : Hs * Es ^ C ≤ B₁ * (H * E ^ A₁) :=
    hb₁ η k k' m side side' hk hk'
  have hcoef : (C * max B₀ B₁) * E ^ (max A₀ A₁) ≤ B * E ^ B :=
    (hpack E hE).trans
      (mul_le_mul hbB (Real.rpow_le_rpow_of_exponent_le hE hbB)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB))
  exact (n04NegativeInverse_pair_weight_scalar hC hE hH hB₀.le
    hzero hpositive κ).trans
      (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg hH κ))

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_pair_sample_heightWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_pair_sample_heightWeight
