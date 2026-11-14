module

public import ContinuousFlexibility.Analysis.N04RealizationFiniteScalarComposition
public import ContinuousFlexibility.Analysis.N04RealizationParameterRescale

/-!
# Scalar composition with a finite parameter loss

The same rescaling of every direction removes the interpolation cost
linear in the parameter order. Restoring the directions charges that
cost once at the order of the resulting genuine multilinear map.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The scalar composition estimate retains the spatial order and the
parameter cost of a finite prefix without enlarging the low seminorm. -/
theorem n04PrincipalNegative_finiteScalarComposition_shifted_bound
    (k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ (V : Set ℝ), IsOpen V → ∀ (f : X → PolarPoint → ℝ) (g : ℝ → ℝ),
      ∀ F : MixedJetRegularity U Ω f, ContDiffOn ℝ ∞ g V →
      (∀ y ∈ U, MapsTo (f y) Ω V) →
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun p => g (f y p)) q),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ s shift : ℕ, ∀ H M R : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ R →
      (∀ m : ℕ, m ≤ a + b → ∀ j : ℕ, j ≤ k →
        ‖iteratedFDeriv ℝ j (iteratedDeriv m g) (f x q)‖ ≤ M) →
      (∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ a + b →
        ∀ z : Fin j → X, (∀ i, P (z i)) →
        ‖((F.parameter u w q hq).D j x z)‖ ≤
          M * parameterHeightWeight H j *
            R ^ (((u + w + shift * j : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      ‖J.D k x v‖ ≤ B * M ^ (k + a + b + 1) *
        parameterHeightWeight H k *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  classical
  obtain ⟨B, hB, hb⟩ := n04Realization_finiteScalarComposition_bound
    (X := X) k a b RH
  refine ⟨B, hB, ?_⟩
  intro U hU Ω hΩ V hV f g F hg hmap q hq J x hx P v hv s shift H M R
    hH hHR hM hR houter hsource
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let α : ℝ := (shift : ℝ) / ((s : ℝ) + 1)
  let t : ℝ := R ^ (1 / ((s : ℝ) + 1))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have htpow (n : ℕ) : t ^ n = R ^ ((n : ℝ) / ((s : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast hRpos.le]
    congr 1
    ring
  let P' : X → Prop := fun z => ∃ w, P w ∧ z = R ^ (-α) • w
  let v' : Fin k → X := fun i => R ^ (-α) • v i
  have hv' (i : Fin k) : P' (v' i) := ⟨v i, hv i, rfl⟩
  have hsource' (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ a + b)
      (z : Fin j → X) (hz : ∀ i, P' (z i)) :
      ‖((F.parameter u w q hq).D j x z)‖ ≤
        M * parameterHeightWeight H j * t ^ (u + w) := by
    choose zz hzz hzeq using hz
    have hraw := hsource j hj u w huw zz hzz
    have hexp : (((u + w + shift * j : ℕ) : ℝ) / ((s : ℝ) + 1)) =
        (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1)) + α * (j : ℝ) := by
      dsimp only [α]
      push_cast
      ring
    rw [hexp] at hraw
    have hh := n04Realization_parameter_rescale_bound
      ((F.parameter u w q hq).D j x) zz hRpos α
      (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1))
      (M * parameterHeightWeight H j) hraw
    have hzEq : z = fun i => R ^ (-α) • zz i := funext hzeq
    rw [hzEq, htpow]
    exact hh
  have hraw := hb U hU Ω hΩ V hV f g F hg hmap q hq J x hx
    P' v' hv' H M t hH hHR hM ht houter hsource'
  rw [htpow] at hraw
  have hh := n04Realization_parameter_unscale_bound (J.D k x) v hRpos α
    (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
    (B * M ^ (k + a + b + 1) * parameterHeightWeight H k) hraw
  have hexp : (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) + α * (k : ℝ) =
      (((a + b + shift * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    dsimp only [α]
    push_cast
    ring
  rw [hexp] at hh
  exact hh

end ContinuousFlexibility.Analysis
