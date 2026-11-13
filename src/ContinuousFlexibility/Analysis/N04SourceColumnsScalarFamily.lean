import ContinuousFlexibility.Analysis.N04SourceColumnsScalarComposition
import ContinuousFlexibility.Analysis.N04SourceColumnsPrefix

/-!
# Material envelopes for scalar compositions of current families

The low order is fixed before the parameter order. A finite prefix of
the input towers is interpolated at that order, and the scalar chain rule
is normalized before its coefficient and exponent are packed together.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Scalar composition preserves the positive-order height gain and a
single high seminorm, allowing an order-dependent loss in the input. -/
theorem n04SourceColumns_scalarFamily_oneHigh
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase : ℕ) (L : ℕ → ℕ)
    {U : Set X} {Ω : Set PolarPoint} {V : Set ℝ}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hV : IsOpen V)
    (E H : I → ℝ) (RH : ℝ) (hE : ∀ t, 1 ≤ E t)
    (hH : ∀ t, 0 ≤ H t ∧ H t ≤ RH)
    (f : I → X → PolarPoint → ℝ) (g : ℝ → ℝ)
    (RF : ∀ t, MixedJetRegularity U Ω (f t)) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : ∀ t x, x ∈ U → MapsTo (f t x) Ω V)
    (hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ t q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF t).parameter a b q hq).D k x v| ≤
          B * E t ^ B * parameterHeightWeight (H t) k *
            oneHighVariationWeight p oldBase (s + L k) x v)
    (houter : ∀ N : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ t q, q ∈ Ω → ∀ x ∈ U, ∀ a b : ℕ, a + b ≤ N →
        ‖iteratedFDeriv ℝ a (iteratedDeriv b g) (f t x q)‖ ≤ A * E t ^ A) :
    ∃ base : ℕ, oldBase ≤ base ∧ ∀ k : ℕ, 0 < k → ∃ loss : ℕ,
      ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ t q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun y => g (f t x y)) q),
      ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
        |J.D k x v| ≤ B * E t ^ B * H t *
          oneHighVariationWeight p base (s + loss) x v := by
  have hprefix := n04SourceColumns_prefix_power p hp hI oldBase L E
    (fun k t => parameterHeightWeight (H t) k) hE
    (fun k t => parameterHeightWeight_nonneg (hH t).1 k) f RF hbound
  let base : ℕ := hprefix.choose
  have hbase : oldBase ≤ base := hprefix.choose_spec.1
  refine ⟨base, hbase, fun k hk => ?_⟩
  have hpref := hprefix.choose_spec.2 k
  let shift : ℕ := hpref.choose
  let loss : ℕ := base + shift * k + 1
  refine ⟨loss, fun s => ?_⟩
  have hs := hpref.choose_spec s
  have ho := houter (k + s)
  have hc := n04SourceColumns_scalarComposition_positive_oneHigh (X := X) k s shift RH
  let P : ℝ := 1 + max ho.choose hs.choose
  have hP : 1 ≤ P := le_add_of_nonneg_right
    (ho.choose_spec.1.le.trans (le_max_left _ _))
  have hAP : ho.choose ≤ P := (le_max_left _ _).trans
    (le_add_of_nonneg_left zero_le_one)
  have hBP : hs.choose ≤ P := (le_max_right _ _).trans
    (le_add_of_nonneg_left zero_le_one)
  have hpack := coefficientEnvelope_pack (hc.choose * P ^ (k + s + 1))
    (P * (k + s + 1 : ℕ))
  have hhigh : base + s + shift * k + 1 = s + loss := by
    dsimp only [loss]
    omega
  refine ⟨hpack.choose, hpack.choose_spec.1, ?_⟩
  intro t q hq a b hab J x hx hlow v
  let M : ℝ := P * E t ^ P
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hP
    (Real.one_le_rpow (hE t) (zero_le_one.trans hP))
  have hAPow : ho.choose * E t ^ ho.choose ≤ M :=
    mul_le_mul hAP (Real.rpow_le_rpow_of_exponent_le (hE t) hAP)
      (Real.rpow_nonneg (zero_le_one.trans (hE t)) _) (zero_le_one.trans hP)
  have hBPow : hs.choose * E t ^ hs.choose ≤ M :=
    mul_le_mul hBP (Real.rpow_le_rpow_of_exponent_le (hE t) hBP)
      (Real.rpow_nonneg (zero_le_one.trans (hE t)) _) (zero_le_one.trans hP)
  have hout : ∀ m : ℕ, m ≤ s → ∀ j : ℕ, j ≤ k →
      ‖iteratedFDeriv ℝ j (iteratedDeriv m g) (f t x q)‖ ≤ M :=
    fun m hm j hj => (ho.choose_spec.2 t q hq x hx j m (by omega)).trans hAPow
  have hraw : ∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ s →
      ∀ z : Fin j → X, (∀ i, p base (z i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (s + loss) (x - (0 : X)) ≤ R →
        (∀ i, p (s + loss) (z i) ≤ R) →
        ‖((RF t).parameter u w q hq).D j x z‖ ≤
          M * parameterHeightWeight (H t) j *
            R ^ (((u + w + shift * j : ℕ) : ℝ) /
              (((s + shift * k : ℕ) : ℝ) + 1)) := by
    intro j hj u w huw z hz R hR hxR hzR
    have hxR' : p (base + s + shift * k + 1) x ≤ R := by
      simpa only [hhigh, sub_zero] using hxR
    have hzR' : ∀ i, p (base + s + shift * k + 1) (z i) ≤ R := by
      simpa only [hhigh] using hzR
    have hb := hs.choose_spec.2 j hj t q hq u w huw x hx hlow z hz R hR hxR' hzR'
    rw [Real.norm_eq_abs]
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBPow (parameterHeightWeight_nonneg (hH t).1 j))
      (Real.rpow_nonneg (zero_le_one.trans hR) _))
  have hb := hc.choose_spec.2 p (0 : X) base (s + loss) U hU Ω hΩ V hV
    (f t) g (RF t) hg (hmap t) q hq (H t) M (hH t).1 (hH t).2 hM
    x hx (by simpa only [sub_zero] using hlow) hout hraw
    k le_rfl hk a b hab J v
  have hMp : M ^ (k + s + 1) =
      P ^ (k + s + 1) * E t ^ (P * (k + s + 1 : ℕ)) := by
    dsimp only [M]
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hE t)) P (k + s + 1)]
  have hrest : 0 ≤ H t * oneHighVariationWeight p base (s + loss) x v :=
    mul_nonneg (hH t).1 (oneHighVariationWeight_nonneg _ _ _ _ _)
  have hcpack := mul_le_mul_of_nonneg_right (hpack.choose_spec.2 (E t) (hE t)) hrest
  have hb' : |J.D k x v| ≤ hc.choose * M ^ (k + s + 1) * H t *
      oneHighVariationWeight p base (s + loss) x v := by
    simpa only [Real.norm_eq_abs, sub_zero] using hb
  exact hb'.trans (by simpa only [hMp, mul_assoc] using hcpack)

end ContinuousFlexibility.Analysis
