module

public import ContinuousFlexibility.Analysis.RootCharacteristicFactor
public import ContinuousFlexibility.Analysis.CanonicalTwoEndpointCubicMixed

/-!
# Actual mixed jets under the two root orientations

The physical radial coordinate is a translation or a reflection.
Consequently its pullback preserves absolute mixed jets at every order,
without requiring a smoothness assumption for the locality identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem abs_mixedDerivative_rootProfileShift
    (F : PolarPoint → ℝ) {r σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (a b : ℕ) (p : PolarPoint) :
    |mixedDerivative a b (fun q => F (rootProfileShift r σ q)) p| =
      |mixedDerivative a b F (rootProfileShift r σ p)| := by
  rcases hσ with hσ | hσ
  · subst σ
    have he : (fun q => F (rootProfileShift r 1 q)) = translateRadialField r F := by
      funext q
      simp only [rootProfileShift, one_mul, translateRadialField]
    rw [he, mixedDerivative_translateRadialField]
    simp only [rootProfileShift, one_mul]
  · subst σ
    have he : (fun q => F (rootProfileShift r (-1) q)) = reflectRadialField r F := by
      funext q
      simp only [rootProfileShift, neg_one_mul, sub_eq_add_neg, reflectRadialField]
    rw [he, abs_mixedDerivative_reflectRadialField]
    simp only [rootProfileShift, neg_one_mul, sub_eq_add_neg]

theorem rootProfileShift_mem_symmetric_interval {r σ R : ℝ} {p : PolarPoint}
    (hσ : σ = 1 ∨ σ = -1) (hp : p.1 ∈ Ioo (-R) R) :
    (rootProfileShift r σ p).1 ∈ Ioo (r - R) (r + R) := by
  rcases hσ with hσ | hσ
  · subst σ
    change r - R < r + 1 * p.1 ∧ r + 1 * p.1 < r + R
    constructor <;> linarith [hp.1, hp.2]
  · subst σ
    change r - R < r + (-1) * p.1 ∧ r + (-1) * p.1 < r + R
    constructor <;> linarith [hp.1, hp.2]

end ContinuousFlexibility.Analysis
