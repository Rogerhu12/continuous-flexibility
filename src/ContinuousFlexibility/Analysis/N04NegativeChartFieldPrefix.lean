module

public import ContinuousFlexibility.Analysis.N04NegativeChartFieldPowerControl
public import ContinuousFlexibility.Analysis.N01cEndpointMixedPowerNormalization
public import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# The first spatial derivative of the actual root coefficients

The first derivative is charged to the fixed low order. The remaining
spatial derivatives and the marked state slots retain their fractional
powers. One base works for both actual coefficients and every state
prefix, and the positive state weight is never raised to a new power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

private theorem endpointUnitPower_oneHigh
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {H E : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (hf : EndpointMixedPowerBounds p center base loss U Ω (fun _ _ => 1) H E f)
    (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m a b, a + b ≤ s → ∀ q ∈ Ω m,
      ∀ J : SmoothDirections U (fun x => mixedDerivative a b (f m x) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 → ∀ v : Fin k → X,
        ‖J.D k x v‖ ≤ B * E m q ^ B * parameterHeightWeight (H m q) k *
          oneHighVariationWeight p base (s + loss) (x - center) v := by
  have hraw : ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ m a b, a + b ≤ s → ∀ q ∈ Ω m,
      ∀ J : SmoothDirections U (fun x => mixedDerivative a b (f m x) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 → ∀ v : Fin k → X,
        ‖J.D k x v‖ ≤ C * E m q ^ A * parameterHeightWeight (H m q) k *
          oneHighVariationWeight p base (s + loss) (x - center) v := by
    by_cases hk : k = 0
    · subst k
      obtain ⟨C, A, hC, hA, hb⟩ := hf 0 s
      refine ⟨C, A, hC, hA, fun m a b hab q hq J x hx hlow v => ?_⟩
      let R : ℝ := 1 + p (s + loss) (x - center)
      have hR : 1 ≤ R := le_add_of_nonneg_right (apply_nonneg _ _)
      have hxR : p (s + loss) (x - center) ≤ R := le_add_of_nonneg_left zero_le_one
      have hh := hb m 0 le_rfl a b hab q hq J x hx hlow v
        (fun i => Fin.elim0 i) R hR hxR (fun i => Fin.elim0 i)
      have hM : 0 ≤ C * E m q ^ A :=
        mul_nonneg (zero_le_one.trans hC)
          (Real.rpow_nonneg (zero_le_one.trans (hE m q hq)) _)
      have hh0 : ‖J.D 0 x v‖ ≤
          C * E m q ^ A * R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
        simpa only [one_pow, one_mul, parameterHeightWeight, ↓reduceIte, mul_one] using hh
      have hh' : ‖J.D 0 x v‖ ≤ C * E m q ^ A * R :=
        hh0.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_self_of_one_le hR (spatialOrder_fraction_le_one hab)) hM)
      simpa only [parameterHeightWeight, ↓reduceIte, mul_one,
        oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero, add_zero, R] using hh'
    · obtain ⟨C, A, hC, hA, hb⟩ := hf.positive_oneHigh
        (fun _ _ _ => zero_le_one) hH hE k s
      refine ⟨C, A, hC, hA, fun m a b hab q hq J x hx hlow v => ?_⟩
      simpa only [one_pow, one_mul, parameterHeightWeight, if_neg hk,
        mul_assoc, mul_left_comm, mul_comm] using
        hb m k le_rfl (Nat.pos_of_ne_zero hk) a b hab q hq J x hx hlow v
  obtain ⟨C, A, hC, hA, hb⟩ := hraw
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack C A
  refine ⟨B, hB, fun m a b hab q hq J x hx hlow v => ?_⟩
  exact (hb m a b hab q hq J x hx hlow v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpack (E m q) (hE m q hq))
        (parameterHeightWeight_nonneg (hH m q hq) k))
      (oneHighVariationWeight_nonneg p base (s + loss) (x - center) v))

/-- The value and first derivative are paid at the fixed base. The
remaining spatial order and the state domain stay literal. -/
def N04NegativeChartFirstSpatialBounds
    (p : ℕ → Seminorm ℝ X) (center : X) (base : ℕ)
    (U : Set X) (Ω : I → Set PolarPoint) (H E : I → PolarPoint → ℝ)
    (f : I → X → PolarPoint → ℝ) (K shift : ℕ) : Prop :=
  ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m k, k ≤ K → ∀ a b,
    a + b ≤ s + 1 → ∀ q ∈ Ω m,
    ∀ J : SmoothDirections U (fun x => mixedDerivative a b (f m x) q),
    ∀ x ∈ U, p base (x - center) ≤ 1 →
    ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → p (base + s + shift * K + 1) (x - center) ≤ R →
      (∀ i, p (base + s + shift * K + 1) (v i) ≤ R) →
      ‖J.D k x v‖ ≤ B * E m q ^ B * parameterHeightWeight (H m q) k *
        R ^ (((a + b - 1 + shift * k : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1))

/-- The choice of base and prefix shift is common to every family with
these original indices, in particular to drift and factored speed. -/
theorem n04NegativeChart_firstSpatial_prefix
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (center : X) (oldBase loss : ℕ) (U : Set X)
    (Ω : I → Set PolarPoint) (H E : I → PolarPoint → ℝ)
    (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q) :
    ∃ base : ℕ, oldBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ f : I → X → PolarPoint → ℝ,
      EndpointMixedPowerBounds p center oldBase loss U Ω (fun _ _ => 1) H E f →
        N04NegativeChartFirstSpatialBounds p center base U Ω H E f K shift := by
  classical
  obtain ⟨base, hbase, hprefix⟩ :=
    n04Realization_fixedBase_prefix_power p hp hI oldBase (fun _ => 1 + loss)
  refine ⟨base, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun f hf s => ?_⟩
  let J := Fin (K + 1) × Fin (s + 1)
  choose c hc hb using fun j : J => endpointUnitPower_oneHigh hf hH hE j.1.val (j.2.val + 1)
  let A : ℝ := 1 + ∑ j : J, c j
  have hsum : 0 ≤ ∑ j : J, c j := Finset.sum_nonneg (fun j _ => (hc j).le)
  have hA : 0 < A := by dsimp only [A]; linarith
  have hcA (j : J) : c j ≤ A :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨C, hC, hCb⟩ := hshift s
  obtain ⟨B, hB, hBb⟩ := coefficientEnvelope_pack (A * C) A
  refine ⟨B, hB, ?_⟩
  intro m k hk a b hab q hq T x hx hlow v hv R hR hxR hvR
  have hn : a + b - 1 ≤ s := by omega
  have heq : a + b ≤ a + b - 1 + 1 := by omega
  let j : J := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a + b - 1, Nat.lt_succ_of_le hn⟩)
  have hcoef : c j * E m q ^ c j ≤ A * E m q ^ A :=
    mul_le_mul (hcA j) (Real.rpow_le_rpow_of_exponent_le (hE m q hq) (hcA j))
      (Real.rpow_nonneg (zero_le_one.trans (hE m q hq)) _) hA.le
  have hw := parameterHeightWeight_nonneg (hH m q hq) k
  have hraw : ‖T.D k x v‖ ≤ A * E m q ^ A * parameterHeightWeight (H m q) k *
      oneHighVariationWeight p oldBase (a + b - 1 + (1 + loss)) (x - center) v := by
    have hh := (hb j m a b heq q hq T x hx ((hp hbase (x - center)).trans hlow) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hw)
        (oneHighVariationWeight_nonneg p oldBase (j.2.val + 1 + loss) (x - center) v))
    simpa only [j, Nat.add_assoc] using hh
  have hpower := (oneHighVariationWeight_mono hp hbase le_rfl (x - center) v).trans
    (hCb k hk (a + b - 1) hn (x - center) hlow v hv R hR hxR hvR)
  have hcost : 0 ≤ A * E m q ^ A * parameterHeightWeight (H m q) k :=
    mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (zero_le_one.trans (hE m q hq)) _)) hw
  calc
    _ ≤ A * E m q ^ A * parameterHeightWeight (H m q) k *
        oneHighVariationWeight p oldBase (a + b - 1 + (1 + loss)) (x - center) v := hraw
    _ ≤ A * E m q ^ A * parameterHeightWeight (H m q) k *
        (C * R ^ (((a + b - 1 + shift * k : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1))) := mul_le_mul_of_nonneg_left hpower hcost
    _ = (A * C) * E m q ^ A * parameterHeightWeight (H m q) k *
        R ^ (((a + b - 1 + shift * k : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hBb (E m q) (hE m q hq)) hw)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

namespace N04RealizationStart

def negativeHalfFirstSpatialBounds (W : N04RealizationStart)
    (e : ℕ ≃ N04PieceIndex W.D) (base domainBase K shift : ℕ)
    (f : (AnnularState W.S × ℝ) → ℕ → Bool → PolarPoint → ℝ) : Prop :=
  N04NegativeChartFirstSpatialBounds (pairGrading (stateGrading W.S) realGrading)
    (W.C.referenceState, 0) base (stateNeighborhood W.S W.C domainBase W.negativeHalfStateRadius)
    (fun i : ℕ × Bool => Ioo (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ)
    (fun i _ => W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ))
    (fun i _ => W.T.E0 (W.negativeHalfSample e i.1 i.2))
    (fun i z q => f z i.1 i.2 q) K shift

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {F : NegativeOpticalFactors W e} {base loss : ℕ}

/-- The already constructed actual coefficient controls give both
first-spatial prefixes with one base and the same state shift. -/
theorem FullHalfFieldPowerControl.firstSpatial_prefix
    (P : F.FullHalfFieldPowerControl base loss) :
    ∃ base' : ℕ, base ≤ base' ∧ ∀ K : ℕ, ∃ shift : ℕ,
      W.negativeHalfFirstSpatialBounds e base' base K shift F.fullHalfDrift ∧
      W.negativeHalfFirstSpatialBounds e base' base K shift F.fullHalfSpeed := by
  obtain ⟨base', hb, hp⟩ := n04NegativeChart_firstSpatial_prefix
    (pairGrading (stateGrading W.S) realGrading) (jointStateGrading_monotone W.S)
    (jointStateGrading_hasInterpolation W.hS) (W.C.referenceState, 0) base loss
    (stateNeighborhood W.S W.C base W.negativeHalfStateRadius)
    (fun i : ℕ × Bool => Ioo (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ)
    (fun i _ => W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ))
    (fun i _ => W.T.E0 (W.negativeHalfSample e i.1 i.2))
    (fun i _ _ => Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _)
    (fun _ _ _ => W.floor _)
  refine ⟨base', hb, fun K => ?_⟩
  obtain ⟨shift, hs⟩ := hp K
  exact ⟨shift, hs _ P.1.bounds, hs _ P.2.bounds⟩

end NegativeOpticalFactors
end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.firstSpatial_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.firstSpatial_prefix
