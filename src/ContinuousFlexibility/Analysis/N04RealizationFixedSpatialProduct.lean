module

public import ContinuousFlexibility.Analysis.N01cMixedPowerAlgebra

/-!
# Actual parameter jets with a fixed spatial factor

The fixed reference multiplier contributes only its spatial jets. The
genuine parameter derivative remains entirely on the current factor,
so its height gain is retained without a positive-order product loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X} {Ω : Set PolarPoint} {h : PolarPoint → ℝ}
  {f : X → PolarPoint → ℝ}

/-- A fixed spatial field has the constant genuine parameter tower. -/
def n04Realization_mixedJetRegularity_fixedSpatial
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h Ω) :
    MixedJetRegularity U Ω (fun _ => h) where
  spatial _ _ := hh
  parameter a b q _ := smoothDirections_constant hU (mixedDerivative a b h q)

/-- The mixed Leibniz formula commutes with every genuine parameter
derivative, with all parameter derivatives on the current factor. -/
theorem n04Realization_fixedSpatialProduct_parameterJet_formula
    (hΩ : IsOpen Ω) (hh : ContDiffOn ℝ ∞ h Ω)
    (RF : MixedJetRegularity U Ω f)
    (a b : ℕ) {q : PolarPoint} (hq : q ∈ Ω)
    (J : SmoothDirections U
      (fun x => mixedDerivative a b (fun p => h p * f x p) q))
    (k : ℕ) {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v = ∑ t : Fin (a + 1) × Fin (b + 1),
      ((a.choose t.1.val : ℝ) * (b.choose t.2.val : ℝ) *
        mixedDerivative t.1.val t.2.val h q) *
      ((RF.parameter (a - t.1.val) (b - t.2.val) q hq).D k x v) := by
  apply smoothDirections_D_eq_linearCombination J
    (fun t : Fin (a + 1) × Fin (b + 1) =>
      RF.parameter (a - t.1.val) (b - t.2.val) q hq)
    (fun t => (a.choose t.1.val : ℝ) * (b.choose t.2.val : ℝ) *
      mixedDerivative t.1.val t.2.val h q) ?_ k hx v
  intro y hy
  rw [Fintype.sum_prod_type]
  rw [mixedDerivative_mul_on_open hΩ hh (RF.spatial y hy) a b hq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A fixed spatial prefix bound multiplies the original current-jet
majorant. Its height factor and fractional spatial exponent are kept. -/
theorem n04Realization_fixedSpatialProduct_parameterJet_bound
    (hΩ : IsOpen Ω) (hh : ContDiffOn ℝ ∞ h Ω)
    (RF : MixedJetRegularity U Ω f)
    (a b s k : ℕ) (hab : a + b ≤ s) {q : PolarPoint} (hq : q ∈ Ω)
    (J : SmoothDirections U
      (fun x => mixedDerivative a b (fun p => h p * f x p) q))
    {x : X} (hx : x ∈ U) (v : Fin k → X)
    {A M R : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hfixed : ∀ u w : ℕ, u + w ≤ s → |mixedDerivative u w h q| ≤ A)
    (hbound : ∀ u w : ℕ, u + w ≤ s →
      |(RF.parameter u w q hq).D k x v| ≤
        M * R ^ (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1))) :
    |J.D k x v| ≤ (2 : ℝ) ^ (a + b) * A * M *
      R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  classical
  let I := Fin (a + 1) × Fin (b + 1)
  let c : I → ℝ := fun t => (a.choose t.1.val : ℝ) * (b.choose t.2.val : ℝ)
  let V : ℝ := M * R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hc (t : I) : 0 ≤ c t := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have habsc (t : I) : |c t| = c t := abs_of_nonneg (hc t)
  have hcurrent (t : I) :
      |(RF.parameter (a - t.1.val) (b - t.2.val) q hq).D k x v| ≤ V := by
    have htotal : (a - t.1.val) + (b - t.2.val) ≤ a + b := by omega
    have horder : (((a - t.1.val + (b - t.2.val) : ℕ) : ℝ) / ((s : ℝ) + 1)) ≤
        (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast htotal
    exact (hbound _ _ (htotal.trans hab)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR horder) hM)
  have hfixed' (t : I) : |mixedDerivative t.1.val t.2.val h q| ≤ A :=
    hfixed _ _ (by have := t.1.isLt; have := t.2.isLt; omega)
  have hmass : (∑ t : I, c t) = (2 : ℝ) ^ (a + b) := by
    rw [Fintype.sum_prod_type]
    exact mixedLeibniz_coefficient_sum a b
  rw [n04Realization_fixedSpatialProduct_parameterJet_formula hΩ hh RF a b hq J k hx v]
  calc
    _ ≤ ∑ t : I, c t *
        (|mixedDerivative t.1.val t.2.val h q| *
          |(RF.parameter (a - t.1.val) (b - t.2.val) q hq).D k x v|) := by
      change |∑ t : I, (c t * mixedDerivative t.1.val t.2.val h q) *
        (RF.parameter (a - t.1.val) (b - t.2.val) q hq).D k x v| ≤ _
      simpa only [abs_mul, habsc, mul_assoc] using
        Finset.abs_sum_le_sum_abs
          (fun t : I => (c t * mixedDerivative t.1.val t.2.val h q) *
            (RF.parameter (a - t.1.val) (b - t.2.val) q hq).D k x v) Finset.univ
    _ ≤ ∑ t : I, c t * (A * V) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left
        (mul_le_mul (hfixed' t) (hcurrent t) (abs_nonneg _) hA) (hc t))
    _ = _ := by rw [← Finset.sum_mul, hmass]; dsimp only [V]; ring

end ContinuousFlexibility.Analysis
