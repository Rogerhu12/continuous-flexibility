import ContinuousFlexibility.Analysis.N01RootFieldLocalization
import ContinuousFlexibility.Analysis.ReturnCoefficientParity

/-!
# Reflection of the actual localized root fields

The public total-derivative parity identities for an even height give
the symmetry of the actual root drift and factored speed. The fixed
radial clamp preserves these identities. No root collar, additional
smoothness hypothesis, or new flow is needed for this algebraic step.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem factoredCharacteristicField_reflect
    (wref g w : ℝ → ℝ) {Z : PolarPoint → ℝ}
    (heven : ∀ r θ, Z (r, -θ) = Z (r, θ)) (r σ x θ : ℝ) :
    factoredCharacteristicSpeed wref g w Z r σ (x, -θ) =
        factoredCharacteristicSpeed wref g w Z r σ (x, θ) ∧
      orientedCharacteristicDrift w Z r σ (x, -θ) =
        -orientedCharacteristicDrift w Z r σ (x, θ) := by
  have hk : ∀ s η, heightRadial Z (s, -η) = heightRadial Z (s, η) :=
    radialPartial_of_even Z heven
  have hp : ∀ s η, heightAngular Z (s, -η) = -heightAngular Z (s, η) := by
    intro s η
    simp only [heightAngular, angularPartial_of_even Z heven, neg_div]
  have hkθ := angularPartial_of_even (heightRadial Z) hk (r + σ * x) θ
  have hpθ := angularPartial_of_odd (heightAngular Z) hp (r + σ * x) θ
  have hE : profileEnergy w (r + σ * x, -θ) = profileEnergy w (r + σ * x, θ) := rfl
  have hD : polarDiscriminant w Z (r + σ * x, -θ) =
      polarDiscriminant w Z (r + σ * x, θ) := by
    simp only [polarDiscriminant, heightDiscriminant, hE, hk, hp, neg_sq]
  constructor
  · simp only [factoredCharacteristicSpeed, rootProfileShift, hD, heightQ, hE, hk, hpθ]
  · simp only [orientedCharacteristicDrift, rootProfileShift,
      characteristicDrift, heightQ, hE, hp, hkθ, hk, hpθ, div_eq_mul_inv]
    ring

/-- The actual fields used by the controlled root factory have global
reflection symmetry, including outside the physical input strip. -/
theorem localizedRootFields_reflect
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (r σ : ℝ) {R : ℝ} (hR : 0 < R)
    (z : AnnularState S × ℝ) (x θ : ℝ) :
    localizedRootDrift D S C r σ hR z (x, -θ) =
        -localizedRootDrift D S C r σ hR z (x, θ) ∧
      localizedRootSpeed D S C g r σ hR z (x, -θ) =
        localizedRootSpeed D S C g r σ hR z (x, θ) := by
  let t := circleFlowSmoothTimeClamp (-(R / 2)) (R / 2) (R / 2)
    (neg_le_self (half_pos hR).le) (half_pos hR) x
  have h := factoredCharacteristicField_reflect D.w g (stateProfile D S C z.1)
    (stateHeight_even_of_physical hS C z) r σ t θ
  exact ⟨h.2, h.1⟩

end ContinuousFlexibility.Analysis
