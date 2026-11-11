import ContinuousFlexibility.Analysis.CircleCompositionFaaBounds

/-!
# Circle composition estimates with inverse-jet order budgets

If the kth positive derivative of a lift has size `B k * R^(k-1)`,
each Faà di Bruno partition contributes exactly `R^(b-length)` at
angular order b. The outer field keeps its own component energy and
its own derivative order through the sum over circle labels.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

theorem orderedFinpartition_sum_partSize_sub_one
    {b : ℕ} (c : OrderedFinpartition b) :
    (∑ i, (c.partSize i - 1)) = b - c.length := by
  have hsum : (∑ i, (c.partSize i - 1)) + c.length = b := by
    calc
      _ = (∑ i, (c.partSize i - 1)) + ∑ _i : Fin c.length, 1 := by simp
      _ = ∑ i, (c.partSize i - 1 + 1) := (Finset.sum_add_distrib).symm
      _ = ∑ i, c.partSize i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Nat.sub_add_cancel (c.partSize_pos i)
      _ = b := orderedFinpartition_sum_partSize c
  omega

def circleInversePartitionCoefficient (B : ℕ → ℝ)
    {b : ℕ} (c : OrderedFinpartition b) : ℝ :=
  2 * circleSobolevConstant * ∏ i, B (c.partSize i)

theorem circleInversePartitionCoefficient_nonneg
    {B : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
    {b : ℕ} (c : OrderedFinpartition b) :
    0 ≤ circleInversePartitionCoefficient B c :=
  mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
    (Finset.prod_nonneg (fun i _ => hB (c.partSize i)))

theorem orderedFinpartition_product_scale_bound
    {b : ℕ} (c : OrderedFinpartition b) (v : Fin c.length → ℝ)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∀ i, |v i| ≤ B (c.partSize i) * R ^ (c.partSize i - 1)) :
    (∏ i, |v i|) ≤ (∏ i, B (c.partSize i)) * R ^ (b - c.length) := by
  calc
    _ ≤ ∏ i, B (c.partSize i) * R ^ (c.partSize i - 1) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hv i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        orderedFinpartition_sum_partSize_sub_one]

theorem circleWeighted_comp_abs_le_scaled_partitions
    {T : MaterialData} {γ : ℝ} {u g : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hg : ∀ m, ContDiff ℝ ∞ (g m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) {R : ℝ} (hR : 0 ≤ R) (s : ℕ)
    (hjets : ∀ m n θ, 1 ≤ n → n ≤ s →
      |iteratedDeriv n (g m) θ| ≤ B n * R ^ (n - 1))
    (b k m : ℕ) (hb : b ≤ s) (θ : ℝ) :
    (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
      |iteratedDeriv b (u m ∘ g m) θ| ≤
      ∑ c : OrderedFinpartition b,
        (circleInversePartitionCoefficient B c * R ^ (b - c.length)) *
          Real.sqrt (circleComponentEnergy T γ (c.length + k + 1) u m).toReal := by
  classical
  let w : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  have hw : 0 ≤ w := mul_nonneg (pow_nonneg (hM m) _)
    (Real.rpow_nonneg (hH m) _)
  have hterm (c : OrderedFinpartition b) :
      w * |iteratedDeriv c.length (u m) (g m θ) *
          ∏ i, iteratedDeriv (c.partSize i) (g m) θ| ≤
        (circleInversePartitionCoefficient B c * R ^ (b - c.length)) *
          Real.sqrt (circleComponentEnergy T γ (c.length + k + 1) u m).toReal := by
    have hout := circleWeighted_abs_le_componentEnergy hu (hM m) (hH m)
      (a := c.length) (b := k) (s := c.length + k + 1) le_rfl (g m θ)
    have hin := orderedFinpartition_product_scale_bound c
      (fun i => iteratedDeriv (c.partSize i) (g m) θ) B hB hR
      (fun i => hjets m (c.partSize i) θ (c.partSize_pos i) ((c.partSize_le i).trans hb))
    rw [abs_mul, Finset.abs_prod]
    calc
      _ = (w * |iteratedDeriv c.length (u m) (g m θ)|) *
          ∏ i, |iteratedDeriv (c.partSize i) (g m) θ| := (mul_assoc _ _ _).symm
      _ ≤ (2 * circleSobolevConstant *
          Real.sqrt (circleComponentEnergy T γ (c.length + k + 1) u m).toReal) *
          ((∏ i, B (c.partSize i)) * R ^ (b - c.length)) :=
        mul_le_mul hout hin (Finset.prod_nonneg (fun i _ => abs_nonneg _))
          (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
            (Real.sqrt_nonneg _))
      _ = _ := by unfold circleInversePartitionCoefficient; ring
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    (hu.1 m).1.contDiffAt (hg m).contDiffAt (by simp)]
  calc
    _ ≤ w * ∑ c : OrderedFinpartition b,
        |iteratedDeriv c.length (u m) (g m θ) *
          ∏ i, iteratedDeriv (c.partSize i) (g m) θ| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw
    _ = ∑ c : OrderedFinpartition b, w *
        |iteratedDeriv c.length (u m) (g m θ) *
          ∏ i, iteratedDeriv (c.partSize i) (g m) θ| := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun c _ => hterm c)

theorem circleNorm_comp_le_scaled_partitions
    {T : MaterialData} {γ : ℝ} {u g : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hg : ∀ m, ContDiff ℝ ∞ (g m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) {R : ℝ} (hR : 0 ≤ R) (s : ℕ)
    (hjets : ∀ m n θ, 1 ≤ n → n ≤ s →
      |iteratedDeriv n (g m) θ| ≤ B n * R ^ (n - 1)) :
    circleNorm T γ s (fun m => u m ∘ g m) ≤
      Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
        (Real.pi * (Fintype.card (CircleCompositionTermIndex s) : ℝ) ^ 2)) *
        ∑ i : CircleCompositionTermIndex s,
          (circleInversePartitionCoefficient B i.2 *
            R ^ ((i.1.val 0).val - i.2.length)) *
              circleNorm T γ (circleCompositionTermOrder 0 i) u := by
  classical
  apply circleNorm_le_of_finite_component_envelopes
    (fun _ : CircleCompositionTermIndex s => u)
    (circleCompositionTermOrder 0)
    (fun i : CircleCompositionTermIndex s => circleInversePartitionCoefficient B i.2 *
      R ^ ((i.1.val 0).val - i.2.length))
    (fun _ => hu)
    (fun i => mul_nonneg (circleInversePartitionCoefficient_nonneg hB i.2) (pow_nonneg hR _))
    (fun m => (hu.1 m).1.comp (hg m)) hM hH
  intro m b k horder θ
  let j : CircleJetIndex s :=
    ⟨fun i => if i = 0 then ⟨b, by omega⟩ else ⟨k, by omega⟩, by simpa using horder⟩
  have hpoint := circleWeighted_comp_abs_le_scaled_partitions
    hu hg hM hH B hB hR s hjets b k m (by omega) θ
  apply hpoint.trans
  have hnonneg (j' : CircleJetIndex s) : 0 ≤
      ∑ c : OrderedFinpartition (j'.val 0).val,
        (circleInversePartitionCoefficient B c * R ^ ((j'.val 0).val - c.length)) *
          Real.sqrt (circleComponentEnergy T γ
            (c.length + (j'.val 1).val + 1) u m).toReal :=
    Finset.sum_nonneg (fun c _ => mul_nonneg
      (mul_nonneg (circleInversePartitionCoefficient_nonneg hB c) (pow_nonneg hR _))
      (Real.sqrt_nonneg _))
  have hsingle := Finset.single_le_sum (f := fun j' : CircleJetIndex s =>
      ∑ c : OrderedFinpartition (j'.val 0).val,
        (circleInversePartitionCoefficient B c * R ^ ((j'.val 0).val - c.length)) *
          Real.sqrt (circleComponentEnergy T γ
            (c.length + (j'.val 1).val + 1) u m).toReal)
    (fun j' _ => hnonneg j') (Finset.mem_univ j)
  simpa [Fintype.sum_sigma, circleCompositionTermOrder, j] using hsingle

end ContinuousFlexibility.Statements
