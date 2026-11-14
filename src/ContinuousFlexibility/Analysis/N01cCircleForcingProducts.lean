module

public import ContinuousFlexibility.Analysis.N01cDistributedRadialProducts
public import ContinuousFlexibility.Analysis.OneHighCircleFourierRealAlgebra

/-!
# One-high Sobolev norms of the actual finite forcing products

The finite Leibniz formula is applied to the genuine periodic functions.
Each distributed derivative product uses the existing circle Fourier
estimate.  The resulting constant depends on the number of factors and
the output order, while precisely one factor carries the high Sobolev
norm.  These are the products occurring in the higher variational
forcing of the ordinary flow.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ContDiff ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

/-- The existing canonical circle descent of an actual finite product. -/
def circleProductJet {k : ℕ} (f : Fin (k + 1) → ℝ → ℝ)
    (hp : ∀ i, Function.Periodic (f i) P) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (n : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (fun θ => ∏ i, f i θ)
    (fun θ => Finset.prod_congr rfl (fun i _ => hp i θ))
    (contDiff_prod (fun i _ => hf i)) n

@[simp] theorem circleProductJet_coe_apply {k : ℕ} (f : Fin (k + 1) → ℝ → ℝ)
    (hp : ∀ i, Function.Periodic (f i) P) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (n : ℕ) (θ : ℝ) :
    circleProductJet f hp hf n (θ : AddCircle P) =
      iteratedDeriv n (fun η => ∏ i, f i η) θ :=
  periodicCircleJet_coe_apply _ _ _ _ _

theorem circleProductJet_hasDerivAt {k : ℕ} (f : Fin (k + 1) → ℝ → ℝ)
    (hp : ∀ i, Function.Periodic (f i) P) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun η : ℝ => circleProductJet f hp hf n (η : AddCircle P))
      (circleProductJet f hp hf (n + 1) (θ : AddCircle P)) θ :=
  periodicCircleJet_hasDerivAt _ _ _ _ _

/-- Exact circle-valued Leibniz expansion; the factors are the actual
derivatives of the original functions. -/
theorem circleProductJet_leibniz {k : ℕ} (f : Fin (k + 1) → ℝ → ℝ)
    (hp : ∀ i, Function.Periodic (f i) P) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (n : ℕ) :
    circleProductJet f hp hf n =
      ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) •
        ∏ i, periodicCircleJet (f i) (hp i) (hf i) (radialLeibnizOrders k n d i) := by
  classical
  ext θ
  induction θ using QuotientAddGroup.induction_on
  rename_i η
  simpa only [circleProductJet_coe_apply, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, ContinuousMap.prod_apply, smul_eq_mul,
    periodicCircleJet_coe_apply] using
    iteratedDeriv_finProduct_eq_radialLeibniz k n f η (fun i => (hf i).contDiffAt)

def circleProductLeibnizSize (k n : ℕ) : ℝ :=
  ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ)

theorem circleProductLeibnizSize_nonneg (k n : ℕ) :
    0 ≤ circleProductLeibnizSize k n :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- The actual nth derivative of the product is controlled by one high
factor, at every Sobolev order at least n. -/
theorem circleProductJet_l2_le {k : ℕ} (f : Fin (k + 1) → ℝ → ℝ)
    (hp : ∀ i, Function.Periodic (f i) P) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (n s : ℕ) (hns : n ≤ s) :
    (eLpNorm (circleProductJet f hp hf n) 2 AddCircle.haarAddCircle).toReal ≤
      circleProductLeibnizSize k n *
        ∑ j : Fin (k + 1), circleRealSobolevNorm (s : ℝ)
            (periodicCircleJet (f j) (hp j) (hf j) 0) *
          ∏ i ∈ Finset.univ.erase j,
            circleRealFourierL1Norm (periodicCircleJet (f i) (hp i) (hf i) 0) := by
  classical
  let W : ℝ := ∑ j : Fin (k + 1), circleRealSobolevNorm (s : ℝ)
      (periodicCircleJet (f j) (hp j) (hf j) 0) *
    ∏ i ∈ Finset.univ.erase j,
      circleRealFourierL1Norm (periodicCircleJet (f i) (hp i) (hf i) 0)
  have hterm (d : RadialLeibnizIndex k n) :
      (eLpNorm (∏ i, periodicCircleJet (f i) (hp i) (hf i)
        (radialLeibnizOrders k n d i)) 2 AddCircle.haarAddCircle).toReal ≤ W :=
    circle_real_derivative_product_oneHigh k s
      (fun i => periodicCircleJet (f i) (hp i) (hf i))
      (fun i => periodicCircleJet_hasDerivAt (f i) (hp i) (hf i))
      (radialLeibnizOrders k n d)
      ((radialLeibnizOrders_sum k n d).le.trans hns)
  rw [circleProductJet_leibniz f hp hf n, ContinuousMap.coe_sum]
  apply (circle_l2_sum_le (fun d : RadialLeibnizIndex k n =>
    (radialLeibnizCoefficient k n d : ℝ) •
      ∏ i, periodicCircleJet (f i) (hp i) (hf i)
        (radialLeibnizOrders k n d i))).trans
  calc
    _ = ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) *
        (eLpNorm (∏ i, periodicCircleJet (f i) (hp i) (hf i)
          (radialLeibnizOrders k n d i)) 2 AddCircle.haarAddCircle).toReal := by
      apply Finset.sum_congr rfl
      intro d _
      simpa only [ContinuousMap.coe_smul, ContinuousMap.coe_prod] using
        circle_l2_const_smul
          (∏ i, periodicCircleJet (f i) (hp i) (hf i) (radialLeibnizOrders k n d i))
          (Nat.cast_nonneg (radialLeibnizCoefficient k n d))
    _ ≤ ∑ d : RadialLeibnizIndex k n, (radialLeibnizCoefficient k n d : ℝ) * W :=
      Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (hterm d) (Nat.cast_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; rfl

def circleProductSobolevConstant (P : ℝ) (k s : ℕ) : ℝ :=
  max 1 ((2 : ℝ) ^ s * (circleProductLeibnizSize k 0 + circleProductLeibnizSize k s) *
    circleSobolevEmbeddingConstant P ^ k)

theorem circleProductSobolevConstant_one_le (P : ℝ) (k s : ℕ) :
    1 ≤ circleProductSobolevConstant P k s := le_max_left _ _

/-- One and only one of the actual input factors uses the high norm.
All other factors use H¹, independently of the requested output order. -/
theorem circleProductJet_sobolev_le {k : ℕ} (f : Fin (k + 1) → ℝ → ℝ)
    (hp : ∀ i, Function.Periodic (f i) P) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (circleProductJet f hp hf 0) ≤
      circleProductSobolevConstant P k s *
        ∑ j : Fin (k + 1), circleRealSobolevNorm (s : ℝ)
            (periodicCircleJet (f j) (hp j) (hf j) 0) *
          ∏ i ∈ Finset.univ.erase j,
            circleRealSobolevNorm 1 (periodicCircleJet (f i) (hp i) (hf i) 0) := by
  classical
  let H : Fin (k + 1) → ℝ := fun i =>
    circleRealSobolevNorm (s : ℝ) (periodicCircleJet (f i) (hp i) (hf i) 0)
  let L : Fin (k + 1) → ℝ := fun i =>
    circleRealSobolevNorm 1 (periodicCircleJet (f i) (hp i) (hf i) 0)
  let W : ℝ := ∑ j : Fin (k + 1), H j *
    ∏ i ∈ Finset.univ.erase j,
      circleRealFourierL1Norm (periodicCircleJet (f i) (hp i) (hf i) 0)
  let Q : ℝ := ∑ j : Fin (k + 1), H j * ∏ i ∈ Finset.univ.erase j, L i
  let E : ℝ := circleSobolevEmbeddingConstant P
  let C : ℝ := (2 : ℝ) ^ s *
    (circleProductLeibnizSize k 0 + circleProductLeibnizSize k s)
  have hE : 0 ≤ E := zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (add_nonneg (circleProductLeibnizSize_nonneg k 0) (circleProductLeibnizSize_nonneg k s))
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (circle_real_sobolevNorm_nonneg _ _)
      (Finset.prod_nonneg (fun i _ => circle_real_sobolevNorm_nonneg _ _)))
  have hprod (j : Fin (k + 1)) :
      (∏ i ∈ Finset.univ.erase j,
        circleRealFourierL1Norm (periodicCircleJet (f i) (hp i) (hf i) 0)) ≤
      E ^ k * ∏ i ∈ Finset.univ.erase j, L i := by
    calc
      _ ≤ ∏ i ∈ Finset.univ.erase j, E * L i :=
        Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) (fun i _ =>
          circle_real_fourierL1Norm_le_sobolev_one_of_derivatives
            (periodicCircleJet (f i) (hp i) (hf i))
            (periodicCircleJet_hasDerivAt (f i) (hp i) (hf i)) 0)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hW : W ≤ E ^ k * Q := by
    calc
      W ≤ ∑ j : Fin (k + 1), H j *
          (E ^ k * ∏ i ∈ Finset.univ.erase j, L i) :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hprod j) (circle_real_sobolevNorm_nonneg _ _))
      _ = E ^ k * Q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hbound : circleRealSobolevNorm (s : ℝ) (circleProductJet f hp hf 0) ≤ C * W := by
    calc
      _ ≤ (2 : ℝ) ^ s *
          ((eLpNorm (circleProductJet f hp hf 0) 2 AddCircle.haarAddCircle).toReal +
            (eLpNorm (circleProductJet f hp hf s) 2 AddCircle.haarAddCircle).toReal) :=
        circle_real_sobolevNorm_le_derivative_endpoints (circleProductJet f hp hf)
          (circleProductJet_hasDerivAt f hp hf) s
      _ ≤ (2 : ℝ) ^ s *
          (circleProductLeibnizSize k 0 * W + circleProductLeibnizSize k s * W) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (circleProductJet_l2_le f hp hf 0 s (Nat.zero_le s))
            (circleProductJet_l2_le f hp hf s s le_rfl)) (by positivity)
      _ = C * W := by dsimp only [C]; ring
  calc
    _ ≤ C * W := hbound
    _ ≤ C * (E ^ k * Q) := mul_le_mul_of_nonneg_left hW hC
    _ = (C * E ^ k) * Q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right 1 (C * E ^ k)) hQ

end ContinuousFlexibility.Analysis
