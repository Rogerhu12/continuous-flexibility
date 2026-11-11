import ContinuousFlexibility.Scalar.WeightedProductJets
import ContinuousFlexibility.Scalar.WeightedWeightShift

/-!
# Actual finite products in the weighted height model

The number of factors is chosen after the common base and loss.  First the
material pullback of a product is estimated at the sum of its input weights.
The zero-loss inclusion then returns the actual product to the original
nonnegative weight.  All functions retain the prescribed parity, period, and
support before they are lifted by the frozen decoder.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- At the sum weight, material normalization commutes with the actual finite
product.  This identity also includes the empty product. -/
theorem materialPullback_prod
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) {n : ℕ} (f : Fin n → PolarPoint → ℝ) :
    materialPullback T ((n : ℝ) * γ) (fun p => ∏ i, f i p) =
      fun p => ∏ i, materialPullback T γ (f i) p := by
  classical
  funext p
  obtain ⟨_, hpos, _, _, _, _, _, hInv, _⟩ := hT
  have hH : 0 < T.H (T.radius p.1) := (hpos _ (hInv p.1).1).2.1
  simp only [materialPullback, Finset.prod_mul_distrib]
  rw [← Real.rpow_sum_of_pos hH (fun _ : Fin n => -γ) Finset.univ]
  simp [mul_neg]

/-- The mixed-jet estimate for material products applies to the actual decoded
product at its sum weight, with base and loss fixed before the arity. -/
theorem decodedProduct_weightedJets_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s a b c : ℕ, a + b + c ≤ s →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin (k + 1) → A.Space,
        MemLp
          (weightedPhysicalJet T (((k + 1 : ℕ) : ℝ) * γ) a b c
            (fun p => ∏ i, A.decode (u i) p)) 2 materialCylinderMeasure ∧
        (eLpNorm
          (weightedPhysicalJet T (((k + 1 : ℕ) : ℝ) * γ) a b c
            (fun p => ∏ i, A.decode (u i) p)) 2 materialCylinderMeasure).toReal ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  obtain ⟨base, loss, hbase, hprod⟩ :=
    materialPullback_product_mixedDerivative_oneHigh hT hA hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro k s a b c horder
  obtain ⟨C, hC, hCu⟩ := hprod k s a b c horder
  refine ⟨C, hC, fun u => ?_⟩
  simpa only [weightedPhysicalJet, materialPullback_prod hT γ] using hCu u

/-- A positive number of actual decoded factors has the sum weight.  The
positive arity is used only to preserve vanishing outside the annulus. -/
theorem heightMember_decodedProduct_sumWeight
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (k : ℕ)
    (u : Fin (k + 1) → A.Space) :
    HeightMember D T (((k + 1 : ℕ) : ℝ) * γ)
      (fun p => ∏ i, A.decode (u i) p) := by
  classical
  have hu (i : Fin (k + 1)) := hA.2.2.2.1 (u i)
  refine ⟨contDiffOn_prod (fun i _ => (hu i).1), ?_, ?_, ?_, ?_⟩
  · intro r θ
    exact Finset.prod_congr rfl (fun i _ => (hu i).2.1 r θ)
  · intro p
    exact Finset.prod_congr rfl (fun i _ => (hu i).2.2.1 p)
  · intro p hp
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (k + 1)))
      ((hu 0).2.2.2.1 p hp)
  · intro a b c
    obtain ⟨base, loss, _, hjets⟩ := decodedProduct_weightedJets_oneHigh hT hA hinterp
    obtain ⟨C, _, hCu⟩ := hjets k (a + b + c) a b c le_rfl
    exact (hCu u).1

/-- Aggregating the finite physical jet norm does not change the common base
or loss in the product estimate. -/
theorem decodedProduct_sumWeight_physicalNorm_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin (k + 1) → A.Space,
        physicalNorm T (((k + 1 : ℕ) : ℝ) * γ) s
          (fun p => ∏ i, A.decode (u i) p) ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  classical
  obtain ⟨base, loss, hbase, hjets⟩ := decodedProduct_weightedJets_oneHigh hT hA hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro k s
  have hj (j : JetIndex s) :=
    hjets k s (j.val 0).val (j.val 1).val (j.val 2).val j.property
  choose B hB hBu using hj
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hB j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, ?_⟩
  intro u
  let N : ℝ := ∑ i, A.grading (s + loss) (u i) *
    ∏ j ∈ Finset.univ.erase i, A.grading base (u j)
  have hN : 0 ≤ N := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (apply_nonneg _ _) (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)))
  have hjet (a b c : ℕ) (horder : a + b + c ≤ s) :
      MemLp
        (weightedPhysicalJet T (((k + 1 : ℕ) : ℝ) * γ) a b c
          (fun p => ∏ i, A.decode (u i) p)) 2 materialCylinderMeasure ∧
      (eLpNorm
        (weightedPhysicalJet T (((k + 1 : ℕ) : ℝ) * γ) a b c
          (fun p => ∏ i, A.decode (u i) p)) 2 materialCylinderMeasure).toReal ≤ K * N := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj' :
        MemLp
          (weightedPhysicalJet T (((k + 1 : ℕ) : ℝ) * γ) a b c
            (fun p => ∏ i, A.decode (u i) p)) 2 materialCylinderMeasure ∧
        (eLpNorm
          (weightedPhysicalJet T (((k + 1 : ℕ) : ℝ) * γ) a b c
            (fun p => ∏ i, A.decode (u i) p)) 2 materialCylinderMeasure).toReal ≤ B j * N := by
      simpa [j, N] using hBu j u
    exact ⟨hj'.1, hj'.2.trans (mul_le_mul_of_nonneg_right (hBK j) hN)⟩
  exact (physicalNorm_le_of_weightedJet_bounds (mul_nonneg hK hN)
    (fun a b c horder => (hjet a b c horder).1)
    (fun a b c horder => (hjet a b c horder).2)).trans_eq (by
      dsimp only [N]
      ring)

private theorem product_weight_le {γ : ℝ} (hγ : 0 ≤ γ) (k : ℕ) :
    γ ≤ ((k + 1 : ℕ) : ℝ) * γ := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk hγ

/-- At a nonnegative weight the actual product remains in the same height
space.  In particular no unproved endpoint extension is inserted. -/
theorem heightMember_decodedProduct
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) (k : ℕ)
    (u : Fin (k + 1) → A.Space) :
    HeightMember D T γ (fun p => ∏ i, A.decode (u i) p) :=
  heightMember_weight_shift hT (product_weight_le hγ k)
    (heightMember_decodedProduct_sumWeight hT hA hinterp k u)

/-- Arbitrary finite decoded products obey one common fixed-loss estimate in
the original weight.  Only the constant depends on the arity and output order. -/
theorem decodedProduct_physicalNorm_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin (k + 1) → A.Space,
        physicalNorm T γ s (fun p => ∏ i, A.decode (u i) p) ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  obtain ⟨base, loss, hbase, hprod⟩ :=
    decodedProduct_sumWeight_physicalNorm_oneHigh hT hA hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro k s
  obtain ⟨C, hC, hCu⟩ := hprod k s
  obtain ⟨K, hK, hKf⟩ := physicalNorm_weight_shift_bound hT (product_weight_le hγ k) s
  refine ⟨K * C, mul_nonneg hK hC, fun u => ?_⟩
  exact ((hKf (fun p => ∏ i, A.decode (u i) p)
    (heightMember_decodedProduct_sumWeight hT hA hinterp k u)).trans
    (mul_le_mul_of_nonneg_left (hCu u) hK)).trans_eq (by ring)

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- The actual decoded finite product, represented by its unique element in
the given Sobolev model. -/
def decodedProduct (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ)
    (k : ℕ) (u : Fin (k + 1) → A.Space) : A.Space :=
  liftHeight hA (fun p => ∏ i, A.decode (u i) p)
    (heightMember_decodedProduct hT hA hinterp hγ k u)

theorem decode_decodedProduct
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ)
    (k : ℕ) (u : Fin (k + 1) → A.Space) :
    A.decode (decodedProduct hT hA hinterp hγ k u) =
      fun p => ∏ i, A.decode (u i) p :=
  decode_liftHeight hA _ (heightMember_decodedProduct hT hA hinterp hγ k u)

theorem decodedProduct_oneHigh
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin (k + 1) → A.Space,
        A.grading s (decodedProduct hT hA hinterp hγ k u) ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  obtain ⟨base, loss, hbase, hprod⟩ :=
    decodedProduct_physicalNorm_oneHigh hT hA hinterp hγ
  refine ⟨base, loss, hbase, ?_⟩
  intro k s
  obtain ⟨C, hC, hCu⟩ := hprod k s
  refine ⟨C, hC, fun u => ?_⟩
  rw [sobolevGrading_eq_physicalNorm hA, decode_decodedProduct]
  exact hCu u

end SobolevModelData

end ContinuousFlexibility.Statements
