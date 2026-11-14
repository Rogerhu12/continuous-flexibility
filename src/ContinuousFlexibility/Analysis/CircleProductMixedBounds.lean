module

public import ContinuousFlexibility.Analysis.CircleCompositionFaaBounds
public import ContinuousFlexibility.Analysis.TameInterpolationProducts

/-!
# Joint mixed-order estimates for actual circle products

Leibniz's rule keeps the first factor at order i+1 and the second
factor's component energy at order b-i+k+1. Their sum is b+k+2.
Interpolation is applied only after the complete sum over circles.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleProductMixedCoefficient (A : ℝ) (b i : ℕ) : ℝ :=
  (b.choose i : ℝ) * (2 * circleSobolevConstant * A) * (2 * circleSobolevConstant)

theorem circleProductMixedCoefficient_nonneg {A : ℝ} (hA : 0 ≤ A) (b i : ℕ) :
    0 ≤ circleProductMixedCoefficient A b i := by
  have hs := circleSobolevConstant_nonneg
  unfold circleProductMixedCoefficient
  positivity

private theorem scalar_weighted_product_term_le
    {w c x y P Q U V : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hx : |x| ≤ P * U) (hy : w * |y| ≤ Q * V) :
    w * |c * x * y| ≤ (c * P * Q) * U * V := by
  calc
    _ = c * (|x| * (w * |y|)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc]
      ring
    _ ≤ c * ((P * U) * (Q * V)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hx hy (mul_nonneg hw (abs_nonneg _)) ((abs_nonneg _).trans hx)) hc
    _ = _ := by ring

private theorem scalar_weighted_product_deriv_sum_le
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {w : ℝ} (hw : 0 ≤ w) (b : ℕ) (θ : ℝ) (B : Fin (b + 1) → ℝ)
    (hB : ∀ i : Fin (b + 1),
      w * |(b.choose i.val : ℝ) * iteratedDeriv i.val f θ *
        iteratedDeriv (b - i.val) g θ| ≤ B i) :
    w * |iteratedDeriv b (fun y => f y * g y) θ| ≤ ∑ i, B i := by
  rw [iteratedDeriv_fun_mul (hf.contDiffAt.of_le (by simp))
    (hg.contDiffAt.of_le (by simp)), Finset.sum_range]
  calc
    _ ≤ w * ∑ i : Fin (b + 1),
        |(b.choose i.val : ℝ) * iteratedDeriv i.val f θ *
          iteratedDeriv (b - i.val) g θ| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw
    _ = ∑ i : Fin (b + 1), w *
        |(b.choose i.val : ℝ) * iteratedDeriv i.val f θ *
          iteratedDeriv (b - i.val) g θ| := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hB i)

theorem circleWeighted_product_abs_le_mixed_orders
    (hS : IsCircleModel T γ S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (u v : S.Space) (b k m : ℕ) (θ : ℝ) :
    (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
      |iteratedDeriv b (fun y => S.decode u m y * S.decode v m y) θ| ≤
      ∑ i : Fin (b + 1), circleProductMixedCoefficient A b i.val *
        S.grading (i.val + 1) u *
        Real.sqrt (circleComponentEnergy T γ (b - i.val + k + 1) (S.decode v) m).toReal := by
  classical
  let w : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  have hw : 0 ≤ w := mul_nonneg (pow_nonneg (hM m).le _)
    (Real.rpow_nonneg (hH m).le _)
  have hterm (i : Fin (b + 1)) :
      w * |(b.choose i.val : ℝ) * iteratedDeriv i.val (S.decode u m) θ *
        iteratedDeriv (b - i.val) (S.decode v m) θ| ≤
      circleProductMixedCoefficient A b i.val * S.grading (i.val + 1) u *
        Real.sqrt (circleComponentEnergy T γ (b - i.val + k + 1) (S.decode v) m).toReal := by
    have hin := circleModel_jet_abs_le_material_upper hS hH hA hHA u m i.val θ
    have hout := circleWeighted_abs_le_componentEnergy (hS.2.2.2.1 v)
      (hM m).le (hH m).le
      (a := b - i.val) (b := k) (s := b - i.val + k + 1) le_rfl θ
    exact scalar_weighted_product_term_le hw (Nat.cast_nonneg (b.choose i.val)) hin hout
  exact scalar_weighted_product_deriv_sum_le ((hS.2.2.2.1 u).1 m).1
    ((hS.2.2.2.1 v).1 m).1 hw b θ _ hterm

abbrev CircleProductTermIndex (s : ℕ) :=
  Σ j : CircleJetIndex s, Fin ((j.val 0).val + 1)

def circleProductTermOrder {s : ℕ} (i : CircleProductTermIndex s) : ℕ :=
  (i.1.val 0).val - i.2.val + (i.1.val 1).val + 1

def circleProductTermCoefficient {s : ℕ} (A : ℝ) (i : CircleProductTermIndex s) : ℝ :=
  circleProductMixedCoefficient A (i.1.val 0).val i.2.val

theorem circleProductTerm_orders_le {s : ℕ} (i : CircleProductTermIndex s) :
    (i.2.val + 1) + circleProductTermOrder i ≤ s + 2 := by
  have hi := i.2.isLt
  have hj := i.1.property
  unfold circleProductTermOrder
  omega

theorem circleNorm_product_le_mixed_orders
    (hS : IsCircleModel T γ S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (u v : S.Space) (s : ℕ) :
    circleNorm T γ s (fun m θ => S.decode u m θ * S.decode v m θ) ≤
      Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
        (Real.pi * (Fintype.card (CircleProductTermIndex s) : ℝ) ^ 2)) *
        ∑ i : CircleProductTermIndex s,
          circleProductTermCoefficient A i * S.grading (i.2.val + 1) u *
            circleNorm T γ (circleProductTermOrder i) (S.decode v) := by
  classical
  apply circleNorm_le_of_finite_component_envelopes
    (fun _ : CircleProductTermIndex s => S.decode v) circleProductTermOrder
    (fun i => circleProductTermCoefficient A i * S.grading (i.2.val + 1) u)
    (fun _ => hS.2.2.2.1 v)
    (fun i => mul_nonneg (circleProductMixedCoefficient_nonneg hA _ _) (apply_nonneg _ _))
  · intro m
    exact ((hS.2.2.2.1 u).1 m).1.mul ((hS.2.2.2.1 v).1 m).1
  · exact fun m => (hM m).le
  · exact fun m => (hH m).le
  · intro m b k horder θ
    let j : CircleJetIndex s :=
      ⟨fun i => if i = 0 then ⟨b, by omega⟩ else ⟨k, by omega⟩, by simpa using horder⟩
    apply (circleWeighted_product_abs_le_mixed_orders hS hM hH hA hHA u v b k m θ).trans
    have hnonneg (j' : CircleJetIndex s) : 0 ≤
        ∑ i : Fin ((j'.val 0).val + 1),
          circleProductMixedCoefficient A (j'.val 0).val i.val * S.grading (i.val + 1) u *
            Real.sqrt (circleComponentEnergy T γ
              ((j'.val 0).val - i.val + (j'.val 1).val + 1) (S.decode v) m).toReal :=
      Finset.sum_nonneg (fun i _ => mul_nonneg
        (mul_nonneg (circleProductMixedCoefficient_nonneg hA _ _) (apply_nonneg _ _))
        (Real.sqrt_nonneg _))
    have hj := Finset.single_le_sum
      (f := fun j' : CircleJetIndex s =>
        ∑ i : Fin ((j'.val 0).val + 1),
          circleProductMixedCoefficient A (j'.val 0).val i.val * S.grading (i.val + 1) u *
            Real.sqrt (circleComponentEnergy T γ
              ((j'.val 0).val - i.val + (j'.val 1).val + 1) (S.decode v) m).toReal)
      (fun j' _ => hnonneg j') (Finset.mem_univ j)
    simpa [Fintype.sum_sigma, circleProductTermOrder, circleProductTermCoefficient, j] using hj

/-- Unit low-seminorm bounds suffice for the later homogeneous
multilinear normalization. The extra loss includes the fixed low order. -/
theorem circleNorm_product_unit_growth
    (hS : IsCircleModel T γ S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (hinterp : HasInterpolation S.grading) :
    ∃ base loss : ℕ, base ≤ loss ∧ ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : S.Space,
      S.grading base u ≤ 1 → S.grading base v ≤ 1 →
      circleNorm T γ s (fun m θ => S.decode u m θ * S.decode v m θ) ≤
        C * (1 + S.grading (s + loss) u + S.grading (s + loss) v) := by
  classical
  have hp := gradedSeminorm_monotone (fun i => S.level i) S.bond
  let h := hasInterpolation_mul_local_growth
    S.grading S.grading hp hp hinterp hinterp 2 0 1 1 (by norm_num) (by norm_num)
  let base : ℕ := h.choose
  let loss : ℕ := h.choose_spec.choose
  have hbound := h.choose_spec.choose_spec.2
  refine ⟨base, base + loss, Nat.le_add_right _ _, ?_⟩
  intro s
  let hs := hbound (s + base) (by omega)
  let C : ℝ := hs.choose
  have hC : 0 ≤ C := hs.choose_spec.1
  have hb := hs.choose_spec.2
  let prefactor : ℝ := Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
    (Real.pi * (Fintype.card (CircleProductTermIndex s) : ℝ) ^ 2))
  let total : ℝ := ∑ i : CircleProductTermIndex s, circleProductTermCoefficient A i
  have htotal : 0 ≤ total :=
    Finset.sum_nonneg (fun i _ => circleProductMixedCoefficient_nonneg hA _ _)
  refine ⟨prefactor * total * C,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) htotal) hC, ?_⟩
  intro u v hu hv
  have hterm (i : CircleProductTermIndex s) :
      circleProductTermCoefficient A i * S.grading (i.2.val + 1) u *
          circleNorm T γ (circleProductTermOrder i) (S.decode v) ≤
      circleProductTermCoefficient A i * C *
        (1 + S.grading (s + (base + loss)) u + S.grading (s + (base + loss)) v) := by
    have horder := circleProductTerm_orders_le i
    have hlocal := hb (i.2.val + 1) (circleProductTermOrder i) (by omega) u v hu hv
    have hg := ((circleGrading_le_iff_circleNorm hS (circleProductTermOrder i) v
      (apply_nonneg _ _)).mp (le_refl (S.grading (circleProductTermOrder i) v)))
        (circleProductTermOrder i) le_rfl
    have hcoef : 0 ≤ circleProductTermCoefficient A i :=
      circleProductMixedCoefficient_nonneg hA _ _
    calc
      _ ≤ circleProductTermCoefficient A i *
          (S.grading (i.2.val + 1) u * S.grading (circleProductTermOrder i) v) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hg
          (mul_nonneg hcoef (apply_nonneg _ _))
      _ ≤ circleProductTermCoefficient A i *
          (C * (1 + S.grading (s + base + loss) u + S.grading (s + base + loss) v)) :=
        mul_le_mul_of_nonneg_left hlocal hcoef
      _ = _ := by simp only [Nat.add_assoc, mul_assoc]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hsum' :
      (∑ i : CircleProductTermIndex s,
        circleProductTermCoefficient A i * S.grading (i.2.val + 1) u *
          circleNorm T γ (circleProductTermOrder i) (S.decode v)) ≤
      total * C * (1 + S.grading (s + (base + loss)) u +
        S.grading (s + (base + loss)) v) := by
    simpa only [← Finset.sum_mul, total] using hsum
  exact (circleNorm_product_le_mixed_orders hS hM hH hA hHA u v s).trans
    ((mul_le_mul_of_nonneg_left hsum' (Real.sqrt_nonneg _)).trans_eq
      ((mul_assoc prefactor (total * C) _).symm.trans
        (congrArg (fun r : ℝ => r *
          (1 + S.grading (s + (base + loss)) u + S.grading (s + (base + loss)) v))
          (mul_assoc prefactor total C).symm)))

/-- A coarse bilinear product bound proves continuity before the sharper
interpolation estimate is used. -/
theorem circleNorm_product_coarse_bound
    (hS : IsCircleModel T γ S) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : S.Space,
      circleNorm T γ s (fun m θ => S.decode u m θ * S.decode v m θ) ≤
        C * S.grading (s + 1) u * S.grading (s + 1) v := by
  classical
  let prefactor : ℝ := Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
    (Real.pi * (Fintype.card (CircleProductTermIndex s) : ℝ) ^ 2))
  let total : ℝ := ∑ i : CircleProductTermIndex s, circleProductTermCoefficient A i
  have htotal : 0 ≤ total :=
    Finset.sum_nonneg (fun i _ => circleProductMixedCoefficient_nonneg hA _ _)
  refine ⟨prefactor * total, mul_nonneg (Real.sqrt_nonneg _) htotal, ?_⟩
  intro u v
  have hterm (i : CircleProductTermIndex s) :
      circleProductTermCoefficient A i * S.grading (i.2.val + 1) u *
          circleNorm T γ (circleProductTermOrder i) (S.decode v) ≤
      circleProductTermCoefficient A i * S.grading (s + 1) u * S.grading (s + 1) v := by
    have hi := i.2.isLt
    have hj := i.1.property
    have hinner : i.2.val + 1 ≤ s + 1 := by omega
    have houter : circleProductTermOrder i ≤ s + 1 := by unfold circleProductTermOrder; omega
    have hu := gradedSeminorm_monotone (fun j => S.level j) S.bond hinner u
    have hv := ((circleGrading_le_iff_circleNorm hS (s + 1) v
      (apply_nonneg _ _)).mp (le_refl (S.grading (s + 1) v))) (circleProductTermOrder i) houter
    exact mul_le_mul (mul_le_mul_of_nonneg_left hu
      (circleProductMixedCoefficient_nonneg hA _ _)) hv
      (Real.sqrt_nonneg _) (mul_nonneg (circleProductMixedCoefficient_nonneg hA _ _)
        (apply_nonneg _ _))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hsum' :
      (∑ i : CircleProductTermIndex s,
        circleProductTermCoefficient A i * S.grading (i.2.val + 1) u *
          circleNorm T γ (circleProductTermOrder i) (S.decode v)) ≤
      total * S.grading (s + 1) u * S.grading (s + 1) v := by
    simpa only [← Finset.sum_mul, total] using hsum
  exact (circleNorm_product_le_mixed_orders hS hM hH hA hHA u v s).trans
    ((mul_le_mul_of_nonneg_left hsum' (Real.sqrt_nonneg _)).trans_eq (by ring))

end ContinuousFlexibility.Statements
