import ContinuousFlexibility.Analysis.CircleCompositionFaaBounds
import ContinuousFlexibility.Analysis.TameInterpolationOneAdd

/-!
# Fixed-loss local growth of actual circle chart composition

Faà di Bruno's derivative budget is combined with the frozen global
interpolation property of the physical circle grading. The loss is
chosen before the output order, and all component sums are performed
before interpolation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

theorem interpolationOrderCost_successor_le
    {base loss i : ℕ} (hbase : loss + 2 ≤ base) (hi : 1 ≤ i) :
    interpolationOrderCost base loss (i + 1) ≤ i - 1 := by
  unfold interpolationOrderCost
  split_ifs <;> omega

theorem orderedFinpartition_interpolation_cost
    {b : ℕ} (c : OrderedFinpartition b) {base loss : ℕ}
    (hbase : loss + 2 ≤ base) :
    (∑ i, interpolationOrderCost base loss (c.partSize i + 1)) ≤ b - c.length := by
  have hcost : (∑ i, interpolationOrderCost base loss (c.partSize i + 1)) ≤
      ∑ i, (c.partSize i - 1) :=
    Finset.sum_le_sum (fun i _ => interpolationOrderCost_successor_le hbase (c.partSize_pos i))
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

theorem circleCompositionPartition_cost_bound
    {b : ℕ} (c : OrderedFinpartition b) (n k s base loss : ℕ)
    (hbase : loss + 2 ≤ base) (horder : b + k ≤ s) :
    (∑ i : Fin (c.length + 1), interpolationOrderCost base loss
      (Fin.cons (c.length + n + k + 1) (fun j => c.partSize j + 1) i)) ≤
      (s + (base + n + loss + 2)) - base := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hinner := orderedFinpartition_interpolation_cost c hbase
  have hlength := c.length_le
  by_cases hout : base < c.length + n + k + 1
  · have heq : interpolationOrderCost base loss (c.length + n + k + 1) =
        c.length + n + k + 1 - base + loss := by
      simp only [interpolationOrderCost, if_pos hout]
    rw [heq]
    omega
  · have heq : interpolationOrderCost base loss (c.length + n + k + 1) = 0 := by
      simp only [interpolationOrderCost, if_neg hout]
    rw [heq]
    omega

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

/-- One chain-rule term has a joint local estimate linear in the high
gradings of the chart and outer field. -/
theorem circleCompositionPartition_norm_local_bound
    (hS : IsCircleModel T γ S) {A : ℝ} (hA : 0 ≤ A)
    (base loss n s : ℕ) (hbase : loss + 2 ≤ base)
    (hinterp : ∀ a c : ℕ, base < a → a + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        S.grading a x ≤ C * (S.grading base x) ^ (((c : ℝ) - a - loss) / (c - base)) *
          (S.grading c x) ^ (((a : ℝ) - base + loss) / (c - base)))
    {b k : ℕ} (c : OrderedFinpartition b) (horder : b + k ≤ s)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e u : S.Space,
      S.grading base e ≤ K → S.grading base u ≤ K →
      circleCompositionPartitionCoefficient S A e c *
          circleNorm T γ (c.length + n + k + 1) (S.decode u) ≤
        C * (1 + S.grading (s + (base + n + loss + 2)) e +
          S.grading (s + (base + n + loss + 2)) u) := by
  classical
  let high : ℕ := s + (base + n + loss + 2)
  let orders : Fin (c.length + 1) → ℕ :=
    Fin.cons (c.length + n + k + 1) (fun j => c.partSize j + 1)
  have hhigh : base < high := by dsimp [high]; omega
  have hmax : ∀ i, orders i ≤ s + n + 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · dsimp only [orders, Fin.cons_zero]
      have hl := c.length_le
      omega
    · dsimp only [orders, Fin.cons_succ]
      have hj := c.partSize_le j
      omega
  have horders : ∀ i, base < orders i → orders i + loss < high := by
    intro i hi
    have h := hmax i
    dsimp [high]
    omega
  have hcost : (∑ i, interpolationOrderCost base loss (orders i)) ≤ high - base :=
    circleCompositionPartition_cost_bound c n k s base loss hbase horder
  obtain ⟨C, hC, hb⟩ := finite_product_one_add_interpolation_bound
    (E := fun _ : Fin (c.length + 1) => S.Space)
    (fun _ => S.grading)
    (fun _ => gradedSeminorm_monotone (fun j => S.level j) S.bond)
    base high (fun _ => loss) orders hhigh horders hcost
    (fun _ => hinterp) (fun _ => K) (fun _ => hK)
  let P : ℝ := 1 + 2 * circleSobolevConstant * A
  let L : ℝ := (c.length : ℝ) + 1
  have hP : 0 ≤ P := by
    dsimp [P]
    have hs := circleSobolevConstant_nonneg
    positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hscale : 0 ≤ 2 * circleSobolevConstant * P ^ c.length := by
    exact mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
      (pow_nonneg hP _)
  refine ⟨(2 * circleSobolevConstant * P ^ c.length) * C * L,
    mul_nonneg (mul_nonneg hscale hC) hL, ?_⟩
  intro e u he hu
  have hlow : ∀ i : Fin (c.length + 1),
      S.grading base (Fin.cons u (fun _ : Fin c.length => e) i) ≤ K := by
    intro i
    exact Fin.cases hu (fun _ => he) i
  have hproduct : (1 + S.grading (c.length + n + k + 1) u) *
      (∏ i : Fin c.length, (1 + S.grading (c.partSize i + 1) e)) ≤
      C * (1 + S.grading high u + (c.length : ℝ) * S.grading high e) := by
    simpa only [orders, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, add_assoc] using hb (Fin.cons u (fun _ => e)) hlow
  have houter : circleNorm T γ (c.length + n + k + 1) (S.decode u) ≤
      1 + S.grading (c.length + n + k + 1) u := by
    have hg := ((circleGrading_le_iff_circleNorm hS (c.length + n + k + 1) u
      (apply_nonneg _ _)).mp (le_refl (S.grading (c.length + n + k + 1) u)))
        (c.length + n + k + 1) le_rfl
    linarith
  have hinner : (∏ i : Fin c.length,
      (1 + (2 * circleSobolevConstant * A) * S.grading (c.partSize i + 1) e)) ≤
      P ^ c.length * ∏ i : Fin c.length, (1 + S.grading (c.partSize i + 1) e) := by
    calc
      _ ≤ ∏ i : Fin c.length, P * (1 + S.grading (c.partSize i + 1) e) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          have hs := circleSobolevConstant_nonneg
          positivity
        · intro i hi
          have hp : 0 ≤ S.grading (c.partSize i + 1) e := apply_nonneg _ _
          have hs : 0 ≤ 2 * circleSobolevConstant * A :=
            mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hA
          dsimp [P]
          nlinarith
      _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
  have hQ : 1 + S.grading high u + (c.length : ℝ) * S.grading high e ≤
      L * (1 + S.grading high e + S.grading high u) := by
    have he0 : 0 ≤ S.grading high e := apply_nonneg _ _
    have hu0 : 0 ≤ S.grading high u := apply_nonneg _ _
    have hc0 : 0 ≤ (c.length : ℝ) := Nat.cast_nonneg _
    dsimp [L]
    nlinarith
  calc
    circleCompositionPartitionCoefficient S A e c *
        circleNorm T γ (c.length + n + k + 1) (S.decode u) ≤
        circleCompositionPartitionCoefficient S A e c *
          (1 + S.grading (c.length + n + k + 1) u) :=
      mul_le_mul_of_nonneg_left houter
        (circleCompositionPartitionCoefficient_nonneg hA e c)
    _ ≤ (2 * circleSobolevConstant * P ^ c.length) *
        ((1 + S.grading (c.length + n + k + 1) u) *
          ∏ i : Fin c.length, (1 + S.grading (c.partSize i + 1) e)) := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinner
          (mul_nonneg (by norm_num) circleSobolevConstant_nonneg))
        (show 0 ≤ 1 + S.grading (c.length + n + k + 1) u by positivity)
      simpa only [circleCompositionPartitionCoefficient, mul_assoc, mul_left_comm, mul_comm] using h
    _ ≤ (2 * circleSobolevConstant * P ^ c.length) *
        (C * (1 + S.grading high u + (c.length : ℝ) * S.grading high e)) :=
      mul_le_mul_of_nonneg_left hproduct hscale
    _ ≤ (2 * circleSobolevConstant * P ^ c.length) *
        (C * (L * (1 + S.grading high e + S.grading high u))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ hC) hscale
    _ = _ := by ring

/-- Genuine chart composition, including any fixed number of outer
angular derivatives, has fixed-loss joint local seminorm growth. -/
theorem circleNorm_comp_outerJet_local_growth
    (hS : IsCircleModel T γ S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (hinterp : HasInterpolation S.grading)
    (travel : ℕ → ℝ) (n requestedBase : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ base loss : ℕ, requestedBase ≤ base ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ e u : S.Space,
        S.grading base e ≤ K → S.grading base u ≤ K →
        circleNorm T γ s (fun m => (iteratedDeriv n (S.decode u m)) ∘
          circleAffineLift travel (S.decode e) 1 m) ≤
          C * (1 + S.grading (s + loss) e + S.grading (s + loss) u) := by
  classical
  obtain ⟨bi, li, hi⟩ := hinterp
  let base : ℕ := max requestedBase (max bi (li + 2))
  let loss : ℕ := base + n + li + 2
  have hbi : bi ≤ base := (le_max_left bi _).trans (le_max_right _ _)
  have hbase : li + 2 ≤ base := (le_max_right bi _).trans (le_max_right _ _)
  refine ⟨base, loss, le_max_left _ _, ?_⟩
  intro s hs
  have hterm (i : CircleCompositionTermIndex s) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ e u : S.Space,
        S.grading base e ≤ K → S.grading base u ≤ K →
        circleCompositionPartitionCoefficient S A e i.2 *
            circleNorm T γ (circleCompositionTermOrder n i) (S.decode u) ≤
          C * (1 + S.grading (s + loss) e + S.grading (s + loss) u) :=
    circleCompositionPartition_norm_local_bound hS hA base li n s hbase
      (fun a c ha hac => hi base a c hbi ha hac) i.2 i.1.property K hK
  choose C hC hbound using hterm
  let prefactor : ℝ := Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
    (Real.pi * (Fintype.card (CircleCompositionTermIndex s) : ℝ) ^ 2))
  refine ⟨prefactor * ∑ i, C i,
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun i _ => hC i)), ?_⟩
  intro e u he hu
  have hsum : (∑ i : CircleCompositionTermIndex s,
      circleCompositionPartitionCoefficient S A e i.2 *
        circleNorm T γ (circleCompositionTermOrder n i) (S.decode u)) ≤
      (∑ i, C i) * (1 + S.grading (s + loss) e + S.grading (s + loss) u) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hbound i e u he hu)
  exact (circleNorm_comp_outerJet_le_mixed_orders hS hM hH hA hHA travel e u n s).trans
    ((mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)).trans_eq (by ring))

end ContinuousFlexibility.Statements
