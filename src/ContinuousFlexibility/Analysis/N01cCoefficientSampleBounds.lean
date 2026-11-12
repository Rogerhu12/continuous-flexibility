import ContinuousFlexibility.Analysis.N01cMaterialShiftComparison
import ContinuousFlexibility.Analysis.N01cWeightAbsorption
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# Coefficient sample bounds on an arbitrary parameter space

The finite coefficient index, the physical cell comparison and the final
common multiplier are handled before any concrete state space is supplied.
The actual directional towers are retained throughout the transport.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- Transfer all three genuine coefficient families from physical points
to the prescribed material samples, keeping the same height exponent,
parameter domain, grading, base and loss. -/
theorem coefficientSampleBounds_of_pointBounds
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (p : ℕ → Seminorm ℝ X) (center : X) (base loss : ℕ) (U : Set X)
    (F : Fin 3 → ℕ → ℕ → PolarPoint → X → ℝ)
    (jets : ∀ i a b q, q ∈ annularOpen D → SmoothDirections U (F i a b q))
    (hpoint : ∀ k s : ℕ, ∀ i : Fin 3,
      ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
        ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ annularOpen D,
        ∀ J : SmoothDirections U (F i a b q),
        ∀ z ∈ U, ∀ v : Fin k → X,
          |J.D k z v| ≤ B * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A *
            oneHighVariationWeight p base (s + loss) (z - center) v) :
    ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b q,
      a + b ≤ s → q.1 ∈ D.cells m →
      ∃ J : SmoothDirections U (F i a b q),
        ∀ z ∈ U, ∀ v : Fin k → X,
          |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample m) ^ B *
              oneHighVariationWeight p base (s + loss) (z - center) v := by
  classical
  intro k s
  choose c A hc hA0 hb using (fun i : Fin 3 => hpoint k s i)
  let C0 : ℝ := 1 + ∑ i : Fin 3, c i
  let A0 : ℝ := ∑ i : Fin 3, A i
  have hC0 : 0 < C0 := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hc i).le))
  have hcC (i : Fin 3) : c i ≤ C0 :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAA (i : Fin 3) : A i ≤ A0 :=
    Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ i)
  obtain ⟨Cs, As, hCs, hAs, hsample⟩ :=
    materialCell_weight_comparison hT hRef (3 / 4 : ℝ) A0
  obtain ⟨B, hBpos, habsorb⟩ :=
    exists_sameConstant_materialWeight_bound (C0 * Cs) As (3 / 4 : ℝ)
  refine ⟨B, hBpos, ?_⟩
  intro m i a b q hab hqm
  have hpart : RadialPartition D := hRef.choose_spec.2.1
  have hq : q ∈ annularOpen D := ⟨hpart.2.2.2.1 m hqm, mem_univ _⟩
  have hsm := materialSample_mem_radialCore hT hpart m
  let J := jets i a b q hq
  refine ⟨J, fun z hz v => ?_⟩
  let W : ℝ := oneHighVariationWeight p base (s + loss) (z - center) v
  have hW : 0 ≤ W := oneHighVariationWeight_nonneg _ _ _ _ _
  have hHq : 0 ≤ T.H q.1 ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _
  have hEq : 0 ≤ T.E0 q.1 ^ A i :=
    Real.rpow_nonneg (zero_le_one.trans (hE q.1 hq.1)) _
  have henv :
      c i * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A i ≤
        C0 * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A0 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hcC i) hHq)
      (Real.rpow_le_rpow_of_exponent_le (hE q.1 hq.1) (hAA i))
      hEq (mul_nonneg hC0.le hHq)
  calc
    _ ≤ c i * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A i * W :=
      hb i a b hab q hq J z hz v
    _ ≤ C0 * T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A0 * W :=
      mul_le_mul_of_nonneg_right henv hW
    _ = C0 * (T.H q.1 ^ (3 / 4 : ℝ) * T.E0 q.1 ^ A0) * W := by ring
    _ ≤ C0 * (Cs * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ As) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsample m q.1 hqm).1 hC0.le) hW
    _ = (C0 * Cs) * T.H (T.sample m) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample m) ^ As * W := by ring
    _ ≤ _ := habsorb (T.H (T.sample m)) (T.E0 (T.sample m)) W
      (hT.2.1 _ hsm).2.1.le (hE _ hsm) hW

end ContinuousFlexibility.Analysis
