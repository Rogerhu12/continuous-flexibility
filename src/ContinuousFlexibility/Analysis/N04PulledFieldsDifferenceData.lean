module

public import ContinuousFlexibility.Analysis.N04RealizationDifferenceValue
public import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# Reference differences over an abstract graded parameter space

Integrate the genuine first parameter derivative, then subtract the same
reference in every positive-order tower. The complete scalar calculation
is performed before the concrete physical parameter space is substituted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFieldsCurrentData_scale_cost
    {B C e h : ℝ} (hB : 0 ≤ B) (hC : 1 ≤ C) (he : 1 ≤ e) (hh : 0 ≤ h) :
    C * (B * e ^ B * h) ≤ (C * B) * e ^ (C * B) * h := by
  have hBC : B ≤ C * B := le_mul_of_one_le_left hB hC
  calc
    C * (B * e ^ B * h) = (C * B) * e ^ B * h := by ring
    _ ≤ (C * B) * e ^ (C * B) * h :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le he hBC)
          (mul_nonneg (zero_le_one.trans hC) hB)) hh

private theorem n04PulledFieldsCurrentData_zero_weight
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (x : X) (v : Fin 0 → X) :
    p high x ≤ oneHighVariationWeight p base high x v := by
  simp only [oneHighVariationWeight, Finset.univ_eq_empty, Finset.prod_empty,
    Finset.sum_empty, mul_one, add_zero]
  exact le_add_of_nonneg_left zero_le_one

section Generic

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

private def n04PulledFieldsCurrentData_differenceTower
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ} {f₀ : PolarPoint → ℝ}
    (RF : MixedJetRegularity U Ω f) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (h₀ : ContDiffOn ℝ ∞ f₀ Ω) (i j : ℕ) (q : Ω) :
    SmoothDirections U
      (fun z => mixedDerivative i j (fun y => f z y - f₀ y) q.val) :=
  (smoothDirectionsAdd (RF.parameter i j q.val q.property)
    (smoothDirections_constant hU (-mixedDerivative i j f₀ q.val))).congr
      (fun z hz => by
        rw [mixedDerivative_sub_of_contDiffOn hΩ (RF.spatial z hz) h₀ i j q.property]
        exact (sub_eq_add_neg _ _).symm)

private theorem n04PulledFieldsCurrentData_difference_positive
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ} {f₀ : PolarPoint → ℝ}
    (RF : MixedJetRegularity U Ω f) (hΩ : IsOpen Ω)
    (h₀ : ContDiffOn ℝ ∞ f₀ Ω) (i j : ℕ) (q : Ω)
    (K : SmoothDirections U
      (fun z => mixedDerivative i j (fun y => f z y - f₀ y) q.val))
    {k : ℕ} (hk : 0 < k) {z : X} (hz : z ∈ U) (v : Fin k → X) :
    K.D k z v = (RF.parameter i j q.val q.property).D k z v := by
  let Ksub : SmoothDirections U
      (fun z => mixedDerivative i j (f z) q.val - mixedDerivative i j f₀ q.val) :=
    K.congr (fun z hz =>
      mixedDerivative_sub_of_contDiffOn hΩ (RF.spatial z hz) h₀ i j q.property)
  exact smoothDirections_D_sub_constant (RF.parameter i j q.val q.property) Ksub hk hz v

/-- Integrate the first derivative before instantiating the parameter
grading.  Keeping that grading abstract avoids unfolding its physical
space representation in the scalar cost argument. -/
private theorem n04PulledFieldsCurrentData_value
    {U : Set X} {Ω : Set PolarPoint} {P : ℕ → Prop} {base : ℕ}
    {p : ℕ → Seminorm ℝ X} {E H : ℕ → ℝ}
    {f : X → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hzero : (0 : X) ∈ U) (hp : Monotone p)
    (hsegment : ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (0 : X) + t • z ∈ U)
    (hsmall : ∀ z ∈ U, p base z ≤ 1)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (RF : ∀ m, MixedJetRegularity U Ω (fun z => f z m))
    (hreference : ∀ m, f 0 m = f₀ m)
    (hfirst : ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ v : Fin 1 → X, ∀ m, P m →
      ∀ (q : Ω) (i j : ℕ), i + j ≤ s →
        |((RF m).parameter i j q.val q.property).D 1 z v| ≤
          B * E m ^ B * H m * oneHighVariationWeight p base (s + loss) z v) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ m, P m → ∀ (q : Ω) (i j : ℕ), i + j ≤ s →
        |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val| ≤
          B * E m ^ B * H m * p (s + loss) z := by
  refine ⟨max base hfirst.choose, fun s => ?_⟩
  have hs := hfirst.choose_spec s
  let B : ℝ := hs.choose
  have hB : 0 < B := hs.choose_spec.1
  refine ⟨3 * B, mul_pos (by norm_num) hB, fun z hz m hm q i j hij => ?_⟩
  let high : ℕ := s + max base hfirst.choose
  let M : ℝ := B * E m ^ B * H m
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (hH m)
  have hhigh : s + hfirst.choose ≤ high := Nat.add_le_add_left (le_max_right _ _) s
  have hbound := n04Realization_smoothDirections_difference_value_bound
    ((RF m).parameter i j q.val q.property) p base high 0 z
    (hp (by dsimp only [high]; omega)) (hsegment z hz) (hsmall z hz) hM
    (fun y hy v => by
      have hh := hs.choose_spec.2 y hy v m hm q i j hij
      have hw := oneHighVariationWeight_mono (base := base) (base' := base)
        hp le_rfl hhigh y v
      have hh' := hh.trans (mul_le_mul_of_nonneg_left hw hM)
      simpa only [sub_zero] using hh')
  have hscale := n04PulledFieldsCurrentData_scale_cost hB.le (by norm_num : (1 : ℝ) ≤ 3)
    (hE m) (hH m)
  have h₀ : ContDiffOn ℝ ∞ (f₀ m) Ω := (hreference m) ▸ (RF m).spatial 0 hzero
  have he := mixedDerivative_sub_of_contDiffOn hΩ ((RF m).spatial z hz) h₀ i j q.property
  have hbound' :
      |mixedDerivative i j (f z m) q.val - mixedDerivative i j (f₀ m) q.val| ≤
        (3 * M) * p high z := by
    simpa only [zero_add, hreference m] using hbound
  exact (congrArg abs he).le.trans
    (hbound'.trans (mul_le_mul_of_nonneg_right hscale (apply_nonneg _ _)))

end Generic


/-- The quantitative difference interface over an abstract parameter
space. Its loss is selected before the spatial order. -/
theorem n04PulledFields_differenceData_of_positiveJets
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {Ω : Set PolarPoint} {P : ℕ → Prop} {base : ℕ}
    {p : ℕ → Seminorm ℝ X} {E H : ℕ → ℝ}
    {f : X → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hzero : (0 : X) ∈ U) (hp : Monotone p)
    (hsegment : ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (0 : X) + t • z ∈ U)
    (hsmall : ∀ z ∈ U, p base z ≤ 1)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (RF : ∀ m, MixedJetRegularity U Ω (fun z => f z m))
    (hreference : ∀ m, f 0 m = f₀ m)
    (hparameter : ∀ k : ℕ, 0 < k → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ v : Fin k → X, ∀ m, P m → ∀ (q : Ω) (i j : ℕ), i + j ≤ s →
        |((RF m).parameter i j q.val q.property).D k z v| ≤
          B * E m ^ B * H m * oneHighVariationWeight p base (s + loss) z v) :
    ∃ JD : ∀ m (i j : ℕ) (q : Ω), SmoothDirections U
        (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val),
      (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ z ∈ U, ∀ m, P m → ∀ (q : Ω) (i j : ℕ), i + j ≤ s →
          |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val| ≤
            B * E m ^ B * H m * p (s + loss) z) ∧
      ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ z ∈ U, ∀ v : Fin k → X, ∀ m, P m → ∀ (q : Ω) (i j : ℕ), i + j ≤ s →
          |(JD m i j q).D k z v| ≤
            B * E m ^ B * H m * oneHighVariationWeight p base (s + loss) z v := by
  have hreference_smooth (m : ℕ) : ContDiffOn ℝ ∞ (f₀ m) Ω :=
    (hreference m) ▸ (RF m).spatial 0 hzero
  let JD (m i j : ℕ) (q : Ω) : SmoothDirections U
      (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val) :=
    n04PulledFieldsCurrentData_differenceTower (RF m) hU hΩ (hreference_smooth m) i j q
  have hvalue := n04PulledFieldsCurrentData_value hΩ hzero hp hsegment hsmall hE hH
    RF hreference (hparameter 1 zero_lt_one)
  refine ⟨JD, hvalue, fun k => ?_⟩
  by_cases hk : k = 0
  · subst k
    refine ⟨hvalue.choose, fun s => ?_⟩
    have hs := hvalue.choose_spec s
    refine ⟨hs.choose, hs.choose_spec.1, fun z hz v m hm q i j hij => ?_⟩
    have hcost : 0 ≤ hs.choose * E m ^ hs.choose * H m :=
      mul_nonneg
        (mul_nonneg hs.choose_spec.1.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
        (hH m)
    have hbound := (hs.choose_spec.2 z hz m hm q i j hij).trans
      (mul_le_mul_of_nonneg_left
        (n04PulledFieldsCurrentData_zero_weight p base (s + hvalue.choose) z v) hcost)
    exact (congrArg abs (smoothDirections_D_zero_apply (JD m i j q) hz v)).le.trans hbound
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hd := hparameter k hkpos
    refine ⟨hd.choose, fun s => ?_⟩
    have hs := hd.choose_spec s
    refine ⟨hs.choose, hs.choose_spec.1, fun z hz v m hm q i j hij => ?_⟩
    have heq := n04PulledFieldsCurrentData_difference_positive (RF m) hΩ
      (hreference_smooth m) i j q (JD m i j q) hkpos hz v
    exact (congrArg abs heq).le.trans (hs.choose_spec.2 z hz v m hm q i j hij)

end ContinuousFlexibility.Analysis
