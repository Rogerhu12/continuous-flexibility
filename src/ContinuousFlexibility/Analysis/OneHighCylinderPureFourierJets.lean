module

public import ContinuousFlexibility.Analysis.OneHighCylinderSobolevJetsBasic
public import ContinuousFlexibility.Analysis.OneHighCylinderDerivativeMultiplier

/-!
# Actual pure derivative towers in frequency space

These identities use square integrability only through the finite order
under consideration. The radial and angular towers may be supplied
independently, which is convenient for composition estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem cylinderFourier_radialTower_ae (r : ℕ → (ℝ × AddCircle P) → ℂ)
    (hr : ∀ k, Continuous (r k))
    (hdr : ∀ k (θ : AddCircle P) (x : ℝ),
      HasDerivAt (fun y : ℝ => r k (y, θ)) (r (k + 1) (x, θ)) x)
    (s : ℕ) (hr2 : ∀ k, k ≤ s → MemLp (r k) 2 (cylinderPhysicalMeasure P)) :
    ∀ k : ℕ, ∀ hk : k ≤ s,
      cylinderFourier (r k) (hr k) (hr2 k hk) =ᵐ[cylinderFrequencyMeasure]
        fun ζ => cylinderDerivativeMultiplier P k 0 ζ *
          cylinderFourier (r 0) (hr 0) (hr2 0 (Nat.zero_le s)) ζ := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact Eventually.of_forall fun ζ => by
      simp only [cylinderDerivativeMultiplier_zero_zero, one_mul]
  | succ k ih =>
    intro hk
    have hk' : k ≤ s := (Nat.le_succ k).trans hk
    have he := cylinderFourier_radialDerivative_ae (r k) (r (k + 1))
      (hr k) (hr (k + 1)) (hr2 k hk') (hr2 (k + 1) hk) (hdr k)
    refine he.trans ?_
    filter_upwards [ih hk'] with ζ hζ
    rw [hζ, cylinderDerivativeMultiplier_radial_succ]
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring

theorem cylinderFourier_angularTower_ae (a : ℕ → (ℝ × AddCircle P) → ℂ)
    (ha : ∀ k, Continuous (a k))
    (hda : ∀ k (r x : ℝ),
      HasDerivAt (fun y : ℝ => a k (r, (y : AddCircle P)))
        (a (k + 1) (r, (x : AddCircle P))) x)
    (s : ℕ) (ha2 : ∀ k, k ≤ s → MemLp (a k) 2 (cylinderPhysicalMeasure P)) :
    ∀ k : ℕ, ∀ hk : k ≤ s,
      cylinderFourier (a k) (ha k) (ha2 k hk) =ᵐ[cylinderFrequencyMeasure]
        fun ζ => cylinderDerivativeMultiplier P 0 k ζ *
          cylinderFourier (a 0) (ha 0) (ha2 0 (Nat.zero_le s)) ζ := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact Eventually.of_forall fun ζ => by
      simp only [cylinderDerivativeMultiplier_zero_zero, one_mul]
  | succ k ih =>
    intro hk
    have hk' : k ≤ s := (Nat.le_succ k).trans hk
    have he := cylinderFourier_angularDerivative_ae (a k) (a (k + 1))
      (ha k) (ha (k + 1)) (ha2 k hk') (ha2 (k + 1) hk) (hda k)
    refine he.trans ?_
    filter_upwards [ih hk'] with ζ hζ
    rw [hζ, cylinderDerivativeMultiplier_angular_succ]
    simp only [circlePhysicalFrequency, mul_assoc]

theorem cylinder_norm_frequencyWeighted_le_pure_multipliers
    (F : ℝ × ℤ → ℂ) (s : ℕ) (ζ : ℝ × ℤ) :
    ‖frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P))
      (s : ℝ) F ζ‖ ≤ (3 : ℝ) ^ s *
        (‖F ζ‖ + ‖cylinderDerivativeMultiplier P s 0 ζ * F ζ‖ +
          ‖cylinderDerivativeMultiplier P 0 s ζ * F ζ‖) := by
  rw [cylinder_norm_frequencyWeighted_nat]
  simp only [norm_mul, norm_cylinderDerivativeMultiplier, pow_zero, mul_one, one_mul]
  calc
    _ ≤ ((3 : ℝ) ^ s *
        (1 + |2 * Real.pi * ζ.1| ^ s + |(2 * Real.pi / P) * (ζ.2 : ℝ)| ^ s)) * ‖F ζ‖ :=
      mul_le_mul_of_nonneg_right
        (cylinderFrequencyWeight_nat_pow_le (2 * Real.pi) (2 * Real.pi / P) ζ s) (norm_nonneg _)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
