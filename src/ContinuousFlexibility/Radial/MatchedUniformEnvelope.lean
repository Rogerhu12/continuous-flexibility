module

public import ContinuousFlexibility.Radial.MatchedModeCellBounds
public import ContinuousFlexibility.Radial.MatchedTransitionEnvelope

/-!
# Uniform spatial decay of the actual matching formula

The inputs are estimates for the two regional inverses, their actual
external columns, and the actual matching margin. Combining the existing
matching formula with the extra travel distance removes the transition
index from the final envelope. No bound for the whole inverse is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

theorem matchedMode_actual_spatial_envelope {D : ReferenceData}
    (hD : IsAccumulatingProfile D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (M : ℕ → RadialMatchingData D)
    (hM : ∀ i, ActualMatchedRepresentation D (G i) (M i))
    (transition level : ℕ → ℕ)
    (P : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (Q : ℕ → ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (hQ : ∀ i m U F, modePairing D U (Q i m F) = modePairing D (Q i m U) F)
    {a d C₀ Cₚ Cκ : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hC₀ : 0 < C₀) (hCₚ : 0 < Cₚ) (hCκ : 0 < Cκ)
    (hinner : ∀ i k m,
      ‖P k ∘L (M i).innerInverse ∘L
        matchingSourceInnerCLM D (M i) (actualMatchedRepresentation_localRealizations (hM i)) ∘L
          Q i m‖ ≤ C₀ * Real.exp
            (a * (radialQ (level k) + radialQ (level m)) -
              |radialS (level k) - radialS (level m)|))
    (houter : ∀ i k m,
      ‖P k ∘L (M i).outerInverse ∘L
        matchingSourceOuterCLM D (M i) (actualMatchedRepresentation_localRealizations (hM i)) ∘L
          Q i m‖ ≤ C₀ * Real.exp
            (a * (radialQ (level k) + radialQ (level m)) -
              |radialS (level k) - radialS (level m)|))
    (hPi : ∀ i k t, ‖P k ((M i).innerPoisson t)‖ ≤
      Cₚ * Real.exp (a * (radialQ (level k) + radialQ (transition i)) -
        |radialS (level k) - radialS (transition i)|))
    (hPo : ∀ i k t, ‖P k ((M i).outerPoisson t)‖ ≤
      Cₚ * Real.exp (a * (radialQ (level k) + radialQ (transition i)) -
        |radialS (level k) - radialS (transition i)|))
    (hQi : ∀ i m t, ‖Q i m ((M i).innerPoisson t)‖ ≤
      Cₚ * Real.exp (a * (radialQ (level m) + radialQ (transition i)) -
        |radialS (level m) - radialS (transition i)|))
    (hQo : ∀ i m t, ‖Q i m ((M i).outerPoisson t)‖ ≤
      Cₚ * Real.exp (a * (radialQ (level m) + radialQ (transition i)) -
        |radialS (level m) - radialS (transition i)|))
    (hmargin : ∀ i, 4 / (M i).margin + 1 ≤
      Cκ * Real.exp (d * radialQ (transition i))) :
    ∃ C : ℝ, 0 < C ∧ ∀ i k m,
      ‖P k ∘L G i ∘L Q i m‖ ≤
        C * Real.exp ((3 * a + d) * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|) := by
  obtain ⟨T, hT, htravel⟩ := matchedTransition_column_product ha hd
  refine ⟨2 * C₀ + 176 * Cκ * Cₚ ^ 2 * T, by positivity, ?_⟩
  intro i k m
  let e₀ : ℝ := Real.exp
    (a * (radialQ (level k) + radialQ (level m)) -
      |radialS (level k) - radialS (level m)|)
  let e₁ : ℝ := Real.exp
    ((3 * a + d) * (radialQ (level k) + radialQ (level m)) -
      |radialS (level k) - radialS (level m)|)
  let b (l : ℕ) : ℝ := Cₚ * Real.exp
    (a * (radialQ (level l) + radialQ (transition i)) -
      |radialS (level l) - radialS (transition i)|)
  let κ : ℝ := 4 / (M i).margin
  have hκ : 0 ≤ κ := div_nonneg (by norm_num)
    (actualMatchedRepresentation_matrixBounds (hM i)).1.le
  have hb (l : ℕ) : 0 ≤ b l := by dsimp [b]; positivity
  have he : e₀ ≤ e₁ := by
    apply Real.exp_le_exp.mpr
    have hh := mul_nonneg (show 0 ≤ 2 * a + d by positivity)
      (add_nonneg (radialQ_nonneg (level k)) (radialQ_nonneg (level m)))
    nlinarith only [hh]
  have hbound := matchedMode_actual_opNorm_bound hD (hM i) (P k) (Q i m) (hQ i m)
    (I := C₀ * e₀) (O := C₀ * e₀) (p := b k) (v := b k) (h := b m) (o := b m)
    (by dsimp [e₀]; positivity) (by dsimp [e₀]; positivity)
    (hb k) (hb k) (hb m) (hb m)
    (hinner i k m) (houter i k m) (hPi i k) (hPo i k) (hQi i m) (hQo i m)
  have hcoefficient : (168 * κ + 8) * (b k * b m) ≤
      176 * ((κ + 1) * (b k * b m)) := by
    have h := mul_le_mul_of_nonneg_right
      (show 168 * κ + 8 ≤ 176 * (κ + 1) by linarith) (mul_nonneg (hb k) (hb m))
    nlinarith only [h]
  have hproduct : (κ + 1) * (b k * b m) ≤ Cκ * Cₚ ^ 2 * T * e₁ := by
    calc
      _ ≤ (Cκ * Real.exp (d * radialQ (transition i))) * (b k * b m) :=
        mul_le_mul_of_nonneg_right (hmargin i) (mul_nonneg (hb k) (hb m))
      _ = (Cκ * Cₚ ^ 2) *
          (Real.exp (d * radialQ (transition i)) *
            (Real.exp (a * (radialQ (level k) + radialQ (transition i)) -
                |radialS (level k) - radialS (transition i)|) *
              Real.exp (a * (radialQ (level m) + radialQ (transition i)) -
                |radialS (level m) - radialS (transition i)|))) := by
        dsimp only [b]
        ring
      _ ≤ (Cκ * Cₚ ^ 2) * (T * e₁) :=
        mul_le_mul_of_nonneg_left (htravel (transition i) (level k) (level m)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ C₀ * e₀ + C₀ * e₀ +
        (16 * κ * (b k * b m) + 8 * κ * (b k * b m) +
          (96 * κ + 8) * (b k * b m) + 48 * κ * (b k * b m)) := hbound
    _ = 2 * C₀ * e₀ + (168 * κ + 8) * (b k * b m) := by ring
    _ ≤ 2 * C₀ * e₀ + 176 * ((κ + 1) * (b k * b m)) :=
      add_le_add le_rfl hcoefficient
    _ ≤ 2 * C₀ * e₁ + 176 * (Cκ * Cₚ ^ 2 * T * e₁) :=
      add_le_add (mul_le_mul_of_nonneg_left he (by positivity))
        (mul_le_mul_of_nonneg_left hproduct (by norm_num))
    _ = _ := by ring

end ContinuousFlexibility.Radial
