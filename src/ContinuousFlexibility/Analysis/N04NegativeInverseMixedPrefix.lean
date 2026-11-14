module

public import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
public import ContinuousFlexibility.Analysis.N04RealizationMixedSlotBudget
public import ContinuousFlexibility.Analysis.N01cStateAngleGraphBudget

/-!
# Recover the actual mixed inverse jets from their pure joint prefix

Spatial differentiation appends physical basis vectors. The exact
original parameter arity remains fixed, so the positive height factor
survives when the joint inverse estimate is turned into current data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

/-- The actual mixed parameter jet retains the height of its original
parameter arity. Appended spatial directions do not enlarge that arity. -/
theorem n04NegativeInverse_mixed_of_pureJoint
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (low high : Seminorm ℝ E) {R M H t : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (k a b shift : ℕ) (hk : 0 < k)
    (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    (hraw : ∀ n : ℕ, 0 < n → n ≤ k + a + b →
      ∀ w : StateAngleWord n, w.stateArity = k →
      ∀ v : Fin n → E × PolarPoint,
      (∀ i, low (v i).1 ≤ 1) → (∀ i, high (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
        |J.D n (x, q) v| ≤ M * parameterHeightWeight H k *
          t ^ (w.angleArity + shift * k - 1))
    (Q : SmoothDirections U (fun z => mixedDerivative a b (fun p => f (z, p)) q))
    (v : Fin k → E) (hlow : ∀ i, low (v i) ≤ 1) (hhigh : ∀ i, high (v i) ≤ R) :
    |Q.D k x v| ≤ M * parameterHeightWeight H k * t ^ (a + b + shift * k) := by
  let P : ∀ n : ℕ, (Fin n → E × PolarPoint) → Prop := fun n u =>
    ∃ w : StateAngleWord n, w.stateArity = k ∧
      (∀ i, low (u i).1 ≤ 1) ∧ (∀ i, high (u i).1 ≤ R) ∧
      (∀ i, ‖(u i).2‖ ≤ 1) ∧
      (∀ i, w.isState i = false → (u i).1 = 0) ∧
      (∀ i, w.isState i = true → (u i).2 = 0)
  have hbound (n : ℕ) (hn : n ≤ k + a + b)
      (u : Fin n → E × PolarPoint) (hu : P n u) :
      |J.D n (x, q) u| ≤ M * parameterHeightWeight H k * t ^ (a + b + shift * k) := by
    obtain ⟨w, hw, hl, hh, hp, hs, hsp⟩ := hu
    have hsum := w.arity_sum
    have hnpos : 0 < n := by omega
    have hcost : w.angleArity + shift * k - 1 ≤ a + b + shift * k := by omega
    exact (hraw n hnpos hn w hw u hl hh hp hs hsp).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hcost)
        (mul_nonneg hM (parameterHeightWeight_nonneg hH k)))
  rw [n04Realization_mixedParameter_eq_joint J hU hV hc a b k x hx q hq Q v]
  apply n04Realization_jointMixed_bound_of_stableSlots P
    (fun n u hu => n04Realization_mixedSlots_snoc_with_arity low high (fun r => r = k)
      hR hu (1, 0)
      (by simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, le_refl]))
    (fun n u hu => n04Realization_mixedSlots_snoc_with_arity low high (fun r => r = k)
      hR hu (0, 1)
      (by simp only [Prod.norm_def, norm_one, norm_zero, max_eq_right zero_le_one, le_refl]))
    hV hc x hx q hq J k a b _ hbound (fun i => (v i, 0))
  exact n04Realization_mixedSlots_parameters_with_arity low high (fun r => r = k)
    rfl v hlow hhigh

/-- The common root scale expresses a natural derivative degree as
the original fractional high-seminorm power. -/
theorem n04NegativeInverse_commonScale_pow
    {R : ℝ} (hR : 0 ≤ R) (d N : ℕ) :
    (R ^ (1 / ((N : ℝ) + 1))) ^ d = R ^ ((d : ℝ) / ((N : ℝ) + 1)) := by
  calc
    _ = (R ^ (1 / ((N : ℝ) + 1))) ^ (d : ℝ) := (Real.rpow_natCast _ _).symm
    _ = R ^ ((1 / ((N : ℝ) + 1)) * (d : ℝ)) := (Real.rpow_mul hR _ _).symm
    _ = _ := by congr 1; ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeInverse_mixed_of_pureJoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeInverse_mixed_of_pureJoint
