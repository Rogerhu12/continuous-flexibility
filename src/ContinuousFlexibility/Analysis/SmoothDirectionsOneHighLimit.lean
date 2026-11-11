import ContinuousFlexibility.Analysis.SmoothDirectionsBoundedLimit
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Directional limits with the original one-high-factor bounds

Only the existence and continuity argument uses a larger single
seminorm. Every sharper bound on the interior jets passes unchanged to
their limits by continuity of absolute value.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {ι : Type*} {l : Filter ι} [NeBot l]
  {U : Set E} {f : ι → E → ℝ} {g : E → ℝ}

theorem uniformScalarJetSeminormBounds_of_oneHigh
    (p : ℕ → Seminorm ℝ E) (hp : ∀ n, Continuous (p n)) (hmono : Monotone p)
    (base : ℕ) (high : ℕ → ℕ) (J : ∀ i, SmoothDirections U (f i))
    (hbound : ∀ n, ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, x ∈ U → ∀ v : Fin n → E,
      |(J i).D n x v| ≤ B * oneHighVariationWeight p base (high n) x v) :
    UniformScalarJetSeminormBounds J := by
  intro n
  obtain ⟨B, hB, hb⟩ := hbound n
  let q : Seminorm ℝ E := p (max base (high n))
  refine ⟨q, B * ((n : ℝ) + 1), hp _,
    mul_nonneg hB (add_nonneg (Nat.cast_nonneg n) zero_le_one), ?_⟩
  intro i x hx v
  have hw := oneHighVariationWeight_le_seminorm_product p q base (high n)
    (hmono (le_max_left _ _)) (hmono (le_max_right _ _)) x v
  exact (hb i x hx v).trans (by
    convert mul_le_mul_of_nonneg_left hw hB using 1 <;> ring)

theorem exists_smoothDirections_limit_of_oneHigh_bounds
    (p : ℕ → Seminorm ℝ E) (hp : ∀ n, Continuous (p n)) (hmono : Monotone p)
    (base : ℕ) (high : ℕ → ℕ) (J : ∀ i, SmoothDirections U (f i))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hzero : ∀ x ∈ U, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hbound : ∀ n, ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, x ∈ U → ∀ v : Fin n → E,
      |(J i).D n x v| ≤ B * oneHighVariationWeight p base (high n) x v) :
    ∃ K : SmoothDirections U g, ∀ n x, x ∈ U → ∀ v : Fin n → E,
      Tendsto (fun i => (J i).D n x v) l (𝓝 (K.D n x v)) :=
  exists_smoothDirections_of_uniform_seminorm_bounds J hU hc hzero
    (uniformScalarJetSeminormBounds_of_oneHigh p hp hmono base high J hbound)

theorem abs_directionalJet_limit_le (J : ∀ i, SmoothDirections U (f i))
    (K : SmoothDirections U g) {n : ℕ} {x : E} {v : Fin n → E} {B : ℝ}
    (hlim : Tendsto (fun i => (J i).D n x v) l (𝓝 (K.D n x v)))
    (hbound : ∀ i, |(J i).D n x v| ≤ B) : |K.D n x v| ≤ B :=
  le_of_tendsto hlim.abs (Eventually.of_forall hbound)

end ContinuousFlexibility.Analysis
