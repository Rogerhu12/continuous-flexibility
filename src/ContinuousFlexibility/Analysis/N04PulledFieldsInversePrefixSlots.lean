module

public import ContinuousFlexibility.Analysis.N04PulledFieldsInversePrefixPower
public import ContinuousFlexibility.Analysis.N04PulledFieldsInverseSlotBounds

/-!
# Genuine scalar inverse jets on pure mixed slots

The fixed-base scalar prefix and the exact double spatial expansion use
the same original parameter count. The combinatorial factor is uniform
over the finite total-order prefix and is absorbed into the sampled
coefficient envelope, without changing the height weight or power scale.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04PulledFields_inversePrefix_pureWord
    {ι : Type*} {U : Set X} {I : Set ℝ} {f : ι → X → PolarPoint → ℝ}
    (RF : ∀ i, MixedJetRegularity U (I ×ˢ (univ : Set ℝ)) (f i))
    (hU : IsOpen U) (hcU : Convex ℝ U) (hI : IsOpen I) (hcI : Convex ℝ I)
    (hb : ∀ i a b, UniformScalarJetSeminormBounds
      (fun q : I ×ˢ (univ : Set ℝ) => (RF i).parameter a b q.val q.property))
    (J : ∀ i, SmoothDirections (U ×ˢ (I ×ˢ (univ : Set ℝ)))
      (fun z : X × PolarPoint => f i z.1 z.2))
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hinterp : HasInterpolation p)
    (requestedBase : ℕ) (L : ℕ → ℕ) (E H : ι → ℝ)
    (hE : ∀ i, 1 ≤ E i) (hH : ∀ i, 0 ≤ H i)
    (hjet : ∀ k s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ i (q : I ×ˢ (univ : Set ℝ)) (a b : ℕ), a + b = s → 0 < k + s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF i).parameter a b q.val q.property).D k x v| ≤
          A * E i ^ A * parameterHeightWeight (H i) k *
            oneHighVariationWeight p requestedBase
              ((if k = 0 then s - 1 else s) + L k) x v) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ N : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i (x : X), x ∈ U → p base x ≤ 1 →
      ∀ q ∈ I ×ˢ (univ : Set ℝ), ∀ R : ℝ, 1 ≤ R →
      p (base + N + shift * K + 1) x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → X × PolarPoint,
      (∀ j, p base (v j).1 ≤ 1) →
      (∀ j, p (base + N + shift * K + 1) (v j).1 ≤ R) →
      (∀ j, ‖(v j).2‖ ≤ 1) →
      (∀ j, w.isState j = false → (v j).1 = 0) →
      (∀ j, w.isState j = true → (v j).2 = 0) →
        |(J i).D n (x, q) v| ≤ B * E i ^ B * parameterHeightWeight (H i) w.stateArity *
          (R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))) ^
            (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + shift * K) := by
  obtain ⟨base, hbase, hprefix⟩ := n04PulledFields_inversePrefix_power
    (fun i a b q => (RF i).parameter a b q.val q.property)
    p hp hinterp requestedBase L E H hE hH hjet
  refine ⟨base, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun N => ?_⟩
  obtain ⟨A, hA, hraw⟩ := hshift N
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (A * 2 ^ N) A
  refine ⟨B, hB, fun i x hx hxlow q hq R hR hxhigh n hn hnN w hw v hvlow hvhigh
    hvphysical hvstate hvspatial => ?_⟩
  let t : ℝ := R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))
  let e : ℕ := if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + shift * K
  let C : ℝ := A * E i ^ A * parameterHeightWeight (H i) w.stateArity * t ^ e
  have ht : 0 ≤ t := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hweight := parameterHeightWeight_nonneg (hH i) w.stateArity
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)) hweight)
    (pow_nonneg ht _)
  have hangle : w.angleArity ≤ N := by have hs := w.arity_sum; omega
  have hbound : |(J i).D n (x, q) v| ≤ C * 2 ^ w.angleArity := by
    apply n04PulledFields_mixedJoint_pureSlots_bound (RF i) hU hcU hI hcI (hb i) (J i)
      (fun y => p base y ≤ 1 ∧ p (base + N + shift * K + 1) y ≤ R) w hx hq hC
      (fun a b hab u hu => ?_) v (fun j => ⟨hvlow j, hvhigh j⟩)
      hvphysical hvstate hvspatial
    have hpositive : 0 < w.stateArity + (a + b) := by
      have hs := w.arity_sum
      omega
    have hh := hraw w.stateArity hw a b (hab.le.trans hangle) hpositive i ⟨q, hq⟩
      x hx hxlow u (fun j => (hu j).1) R hR hxhigh (fun j => (hu j).2)
    simpa only [hab, C, t, e] using hh
  calc
    |(J i).D n (x, q) v| ≤ C * 2 ^ w.angleArity := hbound
    _ ≤ C * 2 ^ N := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hangle) hC
    _ = ((A * 2 ^ N) * E i ^ A) * parameterHeightWeight (H i) w.stateArity * t ^ e := by
      dsimp only [C]
      ring
    _ ≤ (B * E i ^ B) * parameterHeightWeight (H i) w.stateArity * t ^ e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hpack (E i) (hE i)) hweight)
        (pow_nonneg ht _)

end ContinuousFlexibility.Analysis
