import ContinuousFlexibility.Analysis.CircleAveragedComposition
import ContinuousFlexibility.Analysis.CircleFiniteEnergyEnvelopes
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Composition estimates retaining the actual derivative orders

The ordinary Faà di Bruno formula is estimated before any orders are
enlarged. Each term keeps the component energy of the outer field at
exactly the order it uses. The remaining chart factors use uniform
pointwise estimates from their actual circle grading.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circle_iteratedDeriv_iteratedDeriv (f : ℝ → ℝ) (a b : ℕ) :
    iteratedDeriv a (iteratedDeriv b f) = iteratedDeriv (a + b) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem orderedFinpartition_sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr c.equivSigma

theorem scalar_affineLift_positive_jet_abs_le
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ)
    {i : ℕ} (hi : 1 ≤ i) (θ : ℝ) :
    |iteratedDeriv i (fun x : ℝ => x + a + f x) θ| ≤
      1 + |iteratedDeriv i f θ| := by
  have heq : (fun x : ℝ => x + a + f x) = fun x => a + (x + f x) := by
    funext x
    ring
  have hj : iteratedDeriv i (fun x : ℝ => x + a + f x) θ =
      iteratedDeriv i (fun x : ℝ => x) θ + iteratedDeriv i f θ := by
    rw [heq, iteratedDeriv_const_add (by omega : 0 < i) a]
    exact iteratedDeriv_fun_add (f := fun x : ℝ => x) (g := f)
      (n := i) (x := θ) contDiffAt_id (hf.contDiffAt.of_le (by simp))
  have hid : |iteratedDeriv i (fun x : ℝ => x) θ| ≤ 1 := by
    rw [iteratedDeriv_fun_id, if_neg (by omega : i ≠ 0)]
    split_ifs <;> norm_num
  rw [hj]
  exact (abs_add_le _ _).trans (add_le_add hid le_rfl)

/-- The global bound keeps the precise angular order, rather than
replacing every derivative by the largest one in a chain-rule formula. -/
theorem circleModel_jet_abs_le_material_upper
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (e : S.Space) (m i : ℕ) (θ : ℝ) :
    |iteratedDeriv i (S.decode e m) θ| ≤
      (2 * circleSobolevConstant * A) * S.grading (i + 1) e := by
  have h := circleModel_iteratedDeriv_abs_le hS hH e m i θ
  apply h.trans
  calc
    (2 * circleSobolevConstant * S.grading (i + 1) e) *
        T.H (T.sample m) ^ γ ≤
      (2 * circleSobolevConstant * S.grading (i + 1) e) * A :=
      mul_le_mul_of_nonneg_left (hHA m)
        (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
          (apply_nonneg _ _))
    _ = _ := by ring

theorem circleAffineLift_jet_abs_le_exact_order
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (travel : ℕ → ℝ) (e : S.Space) (m i : ℕ) (θ : ℝ) (hi : 1 ≤ i) :
    |iteratedDeriv i (circleAffineLift travel (S.decode e) 1 m) θ| ≤
      1 + (2 * circleSobolevConstant * A) * S.grading (i + 1) e := by
  have hscalar := scalar_affineLift_positive_jet_abs_le
    ((hS.2.2.2.1 e).1 m).1 (travel m) hi θ
  have hlift : circleAffineLift travel (S.decode e) 1 m =
      fun x : ℝ => x + travel m + S.decode e m x := by
    funext x
    simp only [circleAffineLift, one_mul]
  have hfirst : |iteratedDeriv i (circleAffineLift travel (S.decode e) 1 m) θ| ≤
      1 + |iteratedDeriv i (S.decode e m) θ| :=
    (congrArg (fun f : ℝ → ℝ => |iteratedDeriv i f θ|) hlift).trans_le hscalar
  exact hfirst.trans (add_le_add le_rfl
    (circleModel_jet_abs_le_material_upper hS hH hA hHA e m i θ))

def circleCompositionPartitionCoefficient
    (S : CircleModelData) (A : ℝ) (e : S.Space)
    {b : ℕ} (c : OrderedFinpartition b) : ℝ :=
  2 * circleSobolevConstant *
    ∏ i, (1 + (2 * circleSobolevConstant * A) * S.grading (c.partSize i + 1) e)

theorem circleCompositionPartitionCoefficient_nonneg
    {A : ℝ} (hA : 0 ≤ A) (e : S.Space)
    {b : ℕ} (c : OrderedFinpartition b) :
    0 ≤ circleCompositionPartitionCoefficient S A e c := by
  unfold circleCompositionPartitionCoefficient
  apply mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
  apply Finset.prod_nonneg
  intro i hi
  exact add_nonneg zero_le_one (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hA)
    (apply_nonneg _ _))

theorem scalar_weighted_abs_mul_prod_le
    {ι : Type*} [Fintype ι] (w a C E : ℝ) (p q : ι → ℝ)
    (hCE : 0 ≤ C * E) (hout : w * |a| ≤ C * E)
    (hin : (∏ i, |p i|) ≤ ∏ i, q i) :
    w * |a * ∏ i, p i| ≤ (C * ∏ i, q i) * E := by
  rw [abs_mul, Finset.abs_prod]
  calc
    _ = (w * |a|) * ∏ i, |p i| := (mul_assoc _ _ _).symm
    _ ≤ (C * E) * ∏ i, q i :=
      mul_le_mul hout hin (Finset.prod_nonneg (fun i _ => abs_nonneg _)) hCE
    _ = _ := by ring

theorem scalar_weighted_comp_le_partition_sum
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (b : ℕ) (θ w : ℝ) (hw : 0 ≤ w) (A : OrderedFinpartition b → ℝ)
    (hb : ∀ c : OrderedFinpartition b,
      w * |iteratedDeriv c.length f (g θ) *
        ∏ i, iteratedDeriv (c.partSize i) g θ| ≤ A c) :
    w * |iteratedDeriv b (f ∘ g) θ| ≤ ∑ c, A c := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hf.contDiffAt hg.contDiffAt (by simp)]
  calc
    _ ≤ w * ∑ c : OrderedFinpartition b,
        |iteratedDeriv c.length f (g θ) * ∏ i, iteratedDeriv (c.partSize i) g θ| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw
    _ = ∑ c : OrderedFinpartition b, w *
        |iteratedDeriv c.length f (g θ) * ∏ i, iteratedDeriv (c.partSize i) g θ| :=
      Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun c _ => hb c)

/-- A chain-rule term is controlled by its own outer derivative energy. -/
theorem circleWeighted_comp_outerJet_abs_le_partitions
    (hS : IsCircleModel T γ S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (travel : ℕ → ℝ) (e u : S.Space) (n b k m : ℕ) (θ : ℝ) :
    (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
      |iteratedDeriv b ((iteratedDeriv n (S.decode u m)) ∘
        circleAffineLift travel (S.decode e) 1 m) θ| ≤
      ∑ c : OrderedFinpartition b, circleCompositionPartitionCoefficient S A e c *
        Real.sqrt (circleComponentEnergy T γ (c.length + n + k + 1) (S.decode u) m).toReal := by
  classical
  let φ : ℝ → ℝ := circleAffineLift travel (S.decode e) 1 m
  let w : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  have hw : 0 ≤ w := mul_nonneg (pow_nonneg (hM m).le _)
    (Real.rpow_nonneg (hH m).le _)
  have hu := hS.2.2.2.1 u
  have hu' : ContDiff ℝ ∞ (iteratedDeriv n (S.decode u m)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv n (hu.1 m).1
  have hφ : ContDiff ℝ ∞ φ :=
    circleAffineLift_contDiff (fun j => ((hS.2.2.2.1 e).1 j).1) travel 1 m
  have hterm (c : OrderedFinpartition b) :
      w * |iteratedDeriv c.length (iteratedDeriv n (S.decode u m)) (φ θ) *
        ∏ i, iteratedDeriv (c.partSize i) φ θ| ≤
      circleCompositionPartitionCoefficient S A e c *
        Real.sqrt (circleComponentEnergy T γ (c.length + n + k + 1) (S.decode u) m).toReal := by
    have hout := circleWeighted_abs_le_componentEnergy hu (hM m).le (hH m).le
      (a := c.length + n) (b := k) (s := c.length + n + k + 1) le_rfl (φ θ)
    have hin : (∏ i, |iteratedDeriv (c.partSize i) φ θ|) ≤
        ∏ i, (1 + (2 * circleSobolevConstant * A) * S.grading (c.partSize i + 1) e) := by
      have hpoint (i : Fin c.length) : |iteratedDeriv (c.partSize i) φ θ| ≤
          1 + (2 * circleSobolevConstant * A) * S.grading (c.partSize i + 1) e :=
        circleAffineLift_jet_abs_le_exact_order (T := T) (γ := γ) (S := S)
          hS hH hA hHA travel e m (c.partSize i) θ (c.partSize_pos i)
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hpoint i)
    have hiter : iteratedDeriv c.length (iteratedDeriv n (S.decode u m)) (φ θ) =
        iteratedDeriv (c.length + n) (S.decode u m) (φ θ) :=
      congrFun (circle_iteratedDeriv_iteratedDeriv (S.decode u m) c.length n) (φ θ)
    have heq := congrArg (fun a : ℝ =>
      w * |a * ∏ i, iteratedDeriv (c.partSize i) φ θ|) hiter
    exact heq.trans_le (scalar_weighted_abs_mul_prod_le w
      (iteratedDeriv (c.length + n) (S.decode u m) (φ θ))
      (2 * circleSobolevConstant)
      (Real.sqrt (circleComponentEnergy T γ (c.length + n + k + 1) (S.decode u) m).toReal)
      (fun i => iteratedDeriv (c.partSize i) φ θ)
      (fun i => 1 + (2 * circleSobolevConstant * A) * S.grading (c.partSize i + 1) e)
      (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
        (Real.sqrt_nonneg _)) hout hin)
  exact scalar_weighted_comp_le_partition_sum hu' hφ b θ w hw
    (fun c => circleCompositionPartitionCoefficient S A e c *
      Real.sqrt (circleComponentEnergy T γ (c.length + n + k + 1) (S.decode u) m).toReal)
    hterm

/-- The finite index only records terms in the existing norm and
chain-rule formulas; it introduces no replacement circle carrier. -/
abbrev CircleCompositionTermIndex (s : ℕ) :=
  Σ j : CircleJetIndex s, OrderedFinpartition (j.val 0).val

def circleCompositionTermOrder {s : ℕ} (n : ℕ) (i : CircleCompositionTermIndex s) : ℕ :=
  i.2.length + n + (i.1.val 1).val + 1

theorem circleNorm_comp_outerJet_le_mixed_orders
    (hS : IsCircleModel T γ S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (travel : ℕ → ℝ) (e u : S.Space) (n s : ℕ) :
    circleNorm T γ s (fun m => (iteratedDeriv n (S.decode u m)) ∘
      circleAffineLift travel (S.decode e) 1 m) ≤
    Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
      (Real.pi * (Fintype.card (CircleCompositionTermIndex s) : ℝ) ^ 2)) *
      ∑ i : CircleCompositionTermIndex s,
        circleCompositionPartitionCoefficient S A e i.2 *
          circleNorm T γ (circleCompositionTermOrder n i) (S.decode u) := by
  classical
  apply circleNorm_le_of_finite_component_envelopes
    (fun _ : CircleCompositionTermIndex s => S.decode u)
    (circleCompositionTermOrder n)
    (fun i : CircleCompositionTermIndex s => circleCompositionPartitionCoefficient S A e i.2)
    (fun _ => hS.2.2.2.1 u)
    (fun i => circleCompositionPartitionCoefficient_nonneg hA e i.2)
  · intro m
    have hu : ContDiff ℝ ∞ (iteratedDeriv n (S.decode u m)) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv n ((hS.2.2.2.1 u).1 m).1
    exact hu.comp (circleAffineLift_contDiff (fun j => ((hS.2.2.2.1 e).1 j).1)
      travel 1 m)
  · exact fun m => (hM m).le
  · exact fun m => (hH m).le
  · intro m b k horder θ
    let j : CircleJetIndex s :=
      ⟨fun i => if i = 0 then ⟨b, by omega⟩ else ⟨k, by omega⟩, by simpa using horder⟩
    have hpoint := circleWeighted_comp_outerJet_abs_le_partitions
      hS hM hH hA hHA travel e u n b k m θ
    apply hpoint.trans
    have hnonneg (j' : CircleJetIndex s) : 0 ≤
        ∑ c : OrderedFinpartition (j'.val 0).val,
          circleCompositionPartitionCoefficient S A e c *
            Real.sqrt (circleComponentEnergy T γ
              (c.length + n + (j'.val 1).val + 1) (S.decode u) m).toReal :=
      Finset.sum_nonneg (fun c _ => mul_nonneg
        (circleCompositionPartitionCoefficient_nonneg hA e c) (Real.sqrt_nonneg _))
    have hj := Finset.single_le_sum (fun j' _ => hnonneg j') (Finset.mem_univ j)
    simpa [Fintype.sum_sigma, circleCompositionTermOrder, j] using hj

end ContinuousFlexibility.Statements
