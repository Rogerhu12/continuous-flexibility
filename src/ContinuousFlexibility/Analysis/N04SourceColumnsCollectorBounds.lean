module

public import ContinuousFlexibility.Analysis.N04SourceColumnsData
public import ContinuousFlexibility.Analysis.N04RealizationDifferenceValue

/-! Abstract bounds used to collect current reference differences. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- At zero displacement the value difference is zero. The scalar
coefficient is kept abstract during the seminorm simplification. -/
theorem n04SourceColumns_mixed_zero_of_bound
    (p : Seminorm ℝ X) (g : PolarPoint → ℝ) (q : PolarPoint) (A : ℝ)
    (h : |mixedDerivative 0 0 g q| ≤ A * p 0) : g q = 0 := by
  have hh : |g q| ≤ 0 := by
    simpa only [spaces_mixedDerivative_zero, map_zero, mul_zero] using h
  exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))

/-- The actual difference tower of one mixed spatial derivative. -/
def n04SourceColumns_differenceTower
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    {f₀ : PolarPoint → ℝ} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (RF : MixedJetRegularity U Ω f) (h₀ : ContDiffOn ℝ ∞ f₀ Ω)
    (i j : ℕ) (q : PolarPoint) (hq : q ∈ Ω) :
    SmoothDirections U (fun z => mixedDerivative i j (fun y => f z y - f₀ y) q) :=
  (smoothDirectionsAdd (RF.parameter i j q hq)
    (smoothDirections_constant hU (-mixedDerivative i j f₀ q))).congr
      (fun z hz => by
        rw [mixedDerivative_sub_of_contDiffOn hΩ (RF.spatial z hz) h₀ i j hq]
        exact (sub_eq_add_neg _ _).symm)

/-- Integrate the first parameter jet on the reference segment after
enlarging only the high seminorm. -/
theorem n04SourceColumns_mixed_difference_value
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    {f₀ : PolarPoint → ℝ} (hΩ : IsOpen Ω)
    (RF : MixedJetRegularity U Ω f) (h₀ : ContDiffOn ℝ ∞ f₀ Ω)
    (hzero : EqOn (f 0) f₀ Ω)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base oldHigh high : ℕ)
    (horder : base ≤ high) (hhigh : oldHigh ≤ high)
    (i j : ℕ) {q : PolarPoint} (hq : q ∈ Ω) {x : X} (hx : x ∈ U)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (0 : X) + t • x ∈ U)
    (hlow : p base x ≤ 1) {M : ℝ} (hM : 0 ≤ M)
    (hfirst : ∀ y ∈ U, ∀ v : Fin 1 → X,
      |(RF.parameter i j q hq).D 1 y v| ≤
        M * oneHighVariationWeight p base oldHigh y v) :
    |mixedDerivative i j (fun y => f x y - f₀ y) q| ≤ (3 * M) * p high x := by
  have hb := n04Realization_smoothDirections_difference_value_bound
    (RF.parameter i j q hq) p base high 0 x (hp horder) hsegment hlow hM
    (fun y hy v => by
      have hm := oneHighVariationWeight_mono hp (le_rfl : base ≤ base) hhigh y v
      simpa only [sub_zero] using
        (hfirst y hy v).trans (mul_le_mul_of_nonneg_left hm hM))
  rw [mixedDerivative_sub_of_contDiffOn hΩ (RF.spatial x hx) h₀ i j hq]
  have he := n07a_mixedDerivative_eqOn hΩ hzero i j hq
  simpa only [zero_add, he] using hb

/-- Absorb the fixed factor from the segment estimate without
simplifying any choice of a material coefficient. -/
theorem n04SourceColumns_pack_difference_value
    {x A B E H W : ℝ} (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hb : (3 * A) * E ^ A ≤ B * E ^ B)
    (hx : x ≤ (3 * (A * E ^ A * H)) * W) :
    x ≤ B * E ^ B * H * W := by
  calc
    x ≤ (3 * (A * E ^ A * H)) * W := hx
    _ = ((3 * A) * E ^ A) * H * W := by ring
    _ ≤ B * E ^ B * H * W :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hH) hW

/-- Turn a vanishing value bound into its zeroth parameter-jet bound. -/
theorem n04SourceColumns_zeroJet_of_value
    {U : Set X} {g : X → ℝ} (J : SmoothDirections U g)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) {M : ℝ} (hM : 0 ≤ M)
    {x : X} (hx : x ∈ U) (v : Fin 0 → X) (hb : |g x| ≤ M * p high x) :
    |J.D 0 x v| ≤ M * oneHighVariationWeight p base high x v := by
  rw [smoothDirections_D_zero_apply J hx v]
  have h := hb.trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left zero_le_one : p high x ≤ 1 + p high x) hM)
  simpa only [oneHighVariationWeight, Finset.univ_eq_empty, Finset.prod_empty,
    Finset.sum_empty, mul_one, add_zero] using h

/-- Positive jets are unchanged by subtracting the fixed reference. -/
theorem n04SourceColumns_positive_difference_jet
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    {f₀ : PolarPoint → ℝ} (hΩ : IsOpen Ω)
    (RF : MixedJetRegularity U Ω f) (h₀ : ContDiffOn ℝ ∞ f₀ Ω)
    (i j : ℕ) {q : PolarPoint} (hq : q ∈ Ω)
    (J : SmoothDirections U (fun z => mixedDerivative i j (fun y => f z y - f₀ y) q))
    {k : ℕ} (hk : 0 < k) {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v = (RF.parameter i j q hq).D k x v := by
  let K := J.congr (fun z hz =>
    mixedDerivative_sub_of_contDiffOn hΩ (RF.spatial z hz) h₀ i j hq)
  exact smoothDirections_D_sub_constant (RF.parameter i j q hq) K hk hx v

end ContinuousFlexibility.Analysis
