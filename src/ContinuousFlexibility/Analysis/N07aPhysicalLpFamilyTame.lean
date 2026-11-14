module

public import ContinuousFlexibility.Analysis.N07aHeightFamilyTame

/-!
# Fixed-loss L² towers for actual physical jets

This version does not impose angular parity on the original physical
field. It is used for the mixed coefficient before angular integration.
The tower and its norm estimate are obtained from the original spatial
jet towers and their one-high physical decay estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FirstCountableTopology E]
  {D : ReferenceData} {T : MaterialData} {U : Set E}
  {p : ℕ → Seminorm ℝ E} {base loss : ℕ} {γ δ : ℝ}
  {f : E → PolarPoint → ℝ}

/-- An actual L²-valued family and its genuine tower, retaining the same
one-high bound at the order of its physical jet. -/
theorem n07a_physicalJetLp_uniformTower
    (hT : IsMaterialData D T) (hU : IsOpen U) (hp : WithSeminorms p)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (q : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) q.val))
    (hJ : ∀ k s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a b : ℕ) (q : annularOpen D), a + b ≤ s →
        ∀ x ∈ U, ∀ v : Fin k → E,
          |(J a b q).D k x v| ≤ B * T.H q.val.1 ^ δ *
            oneHighVariationWeight p base (s + loss) x v)
    (hγδ : γ < δ) (a b c : ℕ) :
    ∃ g : E → CylinderL2, ∃ K : SmoothDirections U g,
      (∀ x ∈ U, (g x : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
        weightedPhysicalJet T γ a b c (f x)) ∧
      ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ U, ∀ v : Fin k → E,
        ‖K.D k x v‖ ≤ B * oneHighVariationWeight p base (a + b + loss) x v := by
  obtain ⟨A, hA, hAb⟩ := n07aWeightedJetTower_decay_bound hT hU hf J γ δ a
  let B : ℕ → ℝ := fun k => (hJ k (a + b)).choose
  have hB (k : ℕ) : 0 ≤ B k := (hJ k (a + b)).choose_spec.1
  have hb (k : ℕ) := (hJ k (a + b)).choose_spec.2
  let G : ∀ k : ℕ, E × (Fin k → E) → ℝ := fun k z =>
    A * B k * oneHighVariationWeight p base (a + b + loss) z.1 z.2
  have hG (k : ℕ) : Continuous (G k) := by
    apply continuous_const.mul
    simpa only [sub_zero] using
      n07a_oneHighVariationWeight_continuous hp base (a + b + loss) k (0 : E)
  have hG0 (k : ℕ) (z : E × (Fin k → E)) : 0 ≤ G k z := by
    dsimp only [G]
    exact mul_nonneg (mul_nonneg hA (hB k))
      (by unfold oneHighVariationWeight; positivity)
  have hbound (k : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E) (q : PolarPoint) :
      |(n07aWeightedJetTower hT hU hf J γ a b c q).D k x v| ≤
        G k (x, v) * n07aMaterialJetMajorant T γ δ c q := by
    have h := hAb b c k x v (B k)
      (oneHighVariationWeight p base (a + b + loss) x v) (hB k)
      (by unfold oneHighVariationWeight; positivity)
      (fun j hj q => hb k j b q (Nat.add_le_add_right hj b) x hx v) q
    exact h.trans_eq (by dsimp only [G, n07aMaterialJetMajorant]; ring)
  let K := n07aWeightedJetLpTower hT hU hf J hγδ a b c G hG hbound
  refine ⟨_, K, ?_, ?_⟩
  · intro x hx
    rw [← K.zero x hx]
    filter_upwards [n07aWeightedJetLpTower_D_ae hT hU hf J hγδ
      a b c G hG hbound 0 hx Fin.elim0] with q hq
    exact hq.trans ((n07aWeightedJetTower hT hU hf J γ a b c q).zero x hx)
  · intro k
    let W := (n07aMaterialJetMajorant_memLp hT hγδ c).toLp
      (n07aMaterialJetMajorant T γ δ c)
    refine ⟨A * B k * ‖W‖, mul_nonneg (mul_nonneg hA (hB k)) (norm_nonneg _),
      fun x hx v => ?_⟩
    exact (n07aWeightedJetLpTower_D_norm_le hT hU hf J hγδ a b c G hG hbound
      k hx v (hG0 k (x, v))).trans_eq (by dsimp only [G, W]; ring)

end ContinuousFlexibility.Analysis
