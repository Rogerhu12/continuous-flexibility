import ContinuousFlexibility.Scalar.WeightedPointwise
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Radial multipliers in the actual weighted jet norms

If every fixed derivative of a radial multiplier is bounded by a constant
times `M^r`, its action costs exactly `r` weighted-jet orders.  The estimate
uses the real radial Leibniz formula and the cylinder L² triangle inequality.
The constants are chosen before the input height.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Multiplying one actual weighted jet by a coefficient bounded by `K M^r`
is controlled by the input jet with `r` additional material weights. -/
theorem weightedPhysicalJet_mul_coefficient_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f)
    (a b c r s : ℕ) (horder : a + b + c + r ≤ s)
    {coefficient : PolarPoint → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hc : AEStronglyMeasurable coefficient materialCylinderMeasure)
    (hcb : ∀ p, |coefficient p| ≤ K * T.M (T.radius p.1) ^ r) :
    MemLp (fun p => coefficient p * weightedPhysicalJet T γ a b c f p)
      2 materialCylinderMeasure ∧
    (eLpNorm (fun p => coefficient p * weightedPhysicalJet T γ a b c f p)
      2 materialCylinderMeasure).toReal ≤ K * physicalNorm T γ s f := by
  have hM (p : PolarPoint) : 0 ≤ T.M (T.radius p.1) := by
    obtain ⟨_, hpos, _, _, _, _, _, hInv, _⟩ := hT
    exact zero_le_one.trans (hpos (T.radius p.1) (hInv p.1).1).2.2.2
  have hs := hf.2.2.2.2 a b (c + r)
  have hg : AEStronglyMeasurable
      (fun p => coefficient p * weightedPhysicalJet T γ a b c f p)
      materialCylinderMeasure := hc.mul (hf.2.2.2.2 a b c).aestronglyMeasurable
  have hpoint (p : PolarPoint) :
      ‖coefficient p * weightedPhysicalJet T γ a b c f p‖ ≤
        K * ‖weightedPhysicalJet T γ a b (c + r) f p‖ := by
    simp only [Real.norm_eq_abs, weightedPhysicalJet, abs_mul,
      abs_of_nonneg (pow_nonneg (hM p) c),
      abs_of_nonneg (pow_nonneg (hM p) (c + r))]
    calc
      |coefficient p| * (T.M (T.radius p.1) ^ c *
          |mixedDerivative a b (materialPullback T γ f) p|) ≤
          (K * T.M (T.radius p.1) ^ r) * (T.M (T.radius p.1) ^ c *
            |mixedDerivative a b (materialPullback T γ f) p|) :=
        mul_le_mul_of_nonneg_right (hcb p)
          (mul_nonneg (pow_nonneg (hM p) c) (abs_nonneg _))
      _ = K * (T.M (T.radius p.1) ^ (c + r) *
          |mixedDerivative a b (materialPullback T γ f) p|) := by rw [pow_add]; ring
  have hpointae : ∀ᵐ p ∂materialCylinderMeasure,
      ‖coefficient p * weightedPhysicalJet T γ a b c f p‖ ≤
        K * ‖weightedPhysicalJet T γ a b (c + r) f p‖ :=
    Eventually.of_forall hpoint
  refine ⟨hs.of_le_mul hg hpointae, ?_⟩
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hg hpointae 2
  have hfinite : ENNReal.ofReal K *
      eLpNorm (weightedPhysicalJet T γ a b (c + r) f) 2 materialCylinderMeasure ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.eLpNorm_lt_top).ne
  have hr := ENNReal.toReal_mono hfinite he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left
    (weightedPhysicalJet_norm_le_physicalNorm hf (a := a) (b := b) (c := c + r)
      (s := s) (by omega)) hK)

/-- A radial factor is constant in the angular Leibniz rule, leaving the
ordinary finite radial Leibniz formula with its actual binomial coefficients. -/
theorem mixedDerivative_radial_mul
    {g : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => g q.1 * f q) p =
      ∑ i : Fin (a + 1), (a.choose i.val : ℝ) * iteratedDeriv i.val g p.1 *
        mixedDerivative (a - i.val) b f p := by
  have hinner (r : ℝ) :
      iteratedDeriv b (fun θ => g r * f (r, θ)) p.2 =
        g r * iteratedDeriv b (fun θ => f (r, θ)) p.2 :=
    iteratedDeriv_const_mul_field (g r) (fun θ => f (r, θ))
  have hslice : ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) := by
    simpa only [mixedDerivative, iteratedDeriv_zero, Function.comp_def, id_eq] using
      (contDiff_mixedDerivative hf 0 b).comp (contDiff_id.prodMk contDiff_const)
  unfold mixedDerivative
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (a.choose i : ℝ) * iteratedDeriv i g p.1 *
      iteratedDeriv (a - i) (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) p.1)
    (a + 1)]
  exact iteratedDeriv_mul (hg.contDiffAt.of_le (by simp)) (hslice.contDiffAt.of_le (by simp))

/-- A radial multiplier with one fixed material-envelope power has that
fixed loss in every actual weighted mixed jet. -/
theorem weightedRadialMultiplier_jet_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {g : ℝ → ℝ}
    (hT : IsMaterialData D T) (hg : ContDiff ℝ ∞ g) (r : ℕ)
    (hgb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv j g x| ≤ C * T.M (T.radius x) ^ r)
    (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      MemLp
        (fun p => T.M (T.radius p.1) ^ c *
          mixedDerivative a b (fun q => g q.1 * materialPullback T γ f q) p)
        2 materialCylinderMeasure ∧
      (eLpNorm
        (fun p => T.M (T.radius p.1) ^ c *
          mixedDerivative a b (fun q => g q.1 * materialPullback T γ f q) p)
        2 materialCylinderMeasure).toReal ≤ C * physicalNorm T γ (a + b + c + r) f := by
  classical
  choose B hB hBx using fun i : Fin (a + 1) => hgb i.val
  let C : Fin (a + 1) → ℝ := fun i => (a.choose i.val : ℝ) * B i
  have hC (i : Fin (a + 1)) : 0 ≤ C i := mul_nonneg (Nat.cast_nonneg _) (hB i)
  let coefficient : Fin (a + 1) → PolarPoint → ℝ := fun i p =>
    (a.choose i.val : ℝ) * iteratedDeriv i.val g p.1
  have hc (i : Fin (a + 1)) : AEStronglyMeasurable (coefficient i) materialCylinderMeasure := by
    have hd : Continuous (fun p : PolarPoint => iteratedDeriv i.val g p.1) := by
      simpa only [Function.comp_def] using
        (ContDiff.continuous_iteratedDeriv i.val hg (by simp)).comp continuous_fst
    exact (hd.const_mul _).aestronglyMeasurable
  have hcb (i : Fin (a + 1)) (p : PolarPoint) :
      |coefficient i p| ≤ C i * T.M (T.radius p.1) ^ r := by
    dsimp [coefficient, C]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (a.choose i.val))]
    exact (mul_le_mul_of_nonneg_left (hBx i p.1) (Nat.cast_nonneg _)).trans_eq (by ring)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro f hf
  let term : Fin (a + 1) → PolarPoint → ℝ := fun i p =>
    coefficient i p * weightedPhysicalJet T γ (a - i.val) b c f p
  have ht (i : Fin (a + 1)) := weightedPhysicalJet_mul_coefficient_bound hT hf
    (a - i.val) b c r (a + b + c + r) (by omega) (hC i) (hc i) (hcb i)
  have heq :
      (fun p => T.M (T.radius p.1) ^ c *
        mixedDerivative a b (fun q => g q.1 * materialPullback T γ f q) p) =
        ∑ i : Fin (a + 1), term i := by
    funext p
    rw [mixedDerivative_radial_mul hg (contDiff_materialPullback hT hf.1),
      Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [term, coefficient, weightedPhysicalJet]
    ring
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun i _ => (ht i).1), ?_⟩
  have hfinite : (∑ i, eLpNorm (term i) 2 materialCylinderMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => (ht i).1.eLpNorm_ne_top)
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_sum_le (f := term) (s := Finset.univ) (p := 2) (μ := materialCylinderMeasure)
      (by norm_num))
  rw [ENNReal.toReal_sum (fun i _ => (ht i).1.eLpNorm_ne_top)] at htri
  apply htri.trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => (ht i).2)

end ContinuousFlexibility.Statements
