import ContinuousFlexibility.Analysis.OneHighCircleRepeatedProducts
import ContinuousFlexibility.Analysis.OneHighPointwiseComposition
import ContinuousFlexibility.Analysis.OneHighL2Domination

/-!
# Uniform scalar smooth-composition estimates on the physical circle

Positive derivatives use the actual Faà di Bruno formula and the full
one-high-factor product estimate. The base-point term uses the derivative
bound on a convex region containing both zero and the input range. The
constants are specified before the input or the outer function is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Function Set
open scoped ENNReal BigOperators ContDiff

variable {P : ℝ} [Fact (0 < P)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem periodic_sub_base_comp {v : ℝ → E} (hp : Periodic v P) (Φ : E → ℝ) :
    Periodic (fun x => Φ (v x) - Φ 0) P := by
  intro x
  dsimp only
  rw [hp x]

theorem contDiff_sub_base_comp {v : ℝ → E} {Φ : E → ℝ} (hv : ContDiff ℝ ∞ v)
    (hΦ : ∀ x, ContDiffAt ℝ ∞ Φ (v x)) :
    ContDiff ℝ ∞ (fun x => Φ (v x) - Φ 0) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    ((hΦ x).comp x hv.contDiffAt).sub contDiffAt_const

/-- Positive-order derivative estimate with an explicit low-norm polynomial.
The smoothness hypothesis is needed only at actual input values. -/
theorem circle_scalar_composition_derivative_l2_le
    (v Φ : ℝ → ℝ) (hp : Periodic v P) (hv : ContDiff ℝ ∞ v)
    (hΦ : ∀ x, ContDiffAt ℝ ∞ Φ (v x))
    {s : ℕ} (hs : 0 < s) {R : ℝ} {B : ℕ → ℝ}
    (hB0 : ∀ m, 0 ≤ B m)
    (hB : ∀ x m, 1 ≤ m → m ≤ s → ‖iteratedDeriv m Φ (v x)‖ ≤ B m)
    (hR : circleRealFourierL1Norm (periodicCircleJet v hp hv 0) ≤ R) :
    (eLpNorm (periodicCircleJet (fun x => Φ (v x) - Φ 0)
      (periodic_sub_base_comp hp Φ) (contDiff_sub_base_comp hv hΦ) s)
        2 AddCircle.haarAddCircle).toReal ≤
      circleScalarCompositionCoefficient s R B *
        circleRealSobolevNorm (s : ℝ) (periodicCircleJet v hp hv 0) := by
  classical
  let f : ℕ → C(AddCircle P, ℝ) := periodicCircleJet v hp hv
  let w : ℕ → C(AddCircle P, ℝ) := periodicCircleJet (fun x => Φ (v x) - Φ 0)
    (periodic_sub_base_comp hp Φ) (contDiff_sub_base_comp hv hΦ)
  let Q (c : OrderedFinpartition s) : C(AddCircle P, ℝ) := ∏ j, f (c.partSize j)
  have hpoint (θ : AddCircle P) : ‖w s θ‖ ≤
      ∑ c : OrderedFinpartition s, B c.length * ‖Q c θ‖ := by
    refine QuotientAddGroup.induction_on θ ?_
    intro x
    have hsub : iteratedDeriv s (fun y => Φ (v y) - Φ 0) x =
        iteratedDeriv s (Φ ∘ v) x := by
      simpa only [sub_eq_add_neg, add_comm, Function.comp_apply] using
        (iteratedDeriv_const_add (f := Φ ∘ v) (x := x) hs (-Φ 0))
    have hc := norm_iteratedDeriv_comp_le_partition_sum (hΦ x) hv.contDiffAt s
    have hc' : ‖iteratedDeriv s (Φ ∘ v) x‖ ≤
        ∑ c : OrderedFinpartition s, B c.length *
          ∏ j, ‖iteratedDeriv (c.partSize j) v x‖ := by
      apply hc.trans
      exact Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_right
          (hB x c.length (c.length_pos hs) c.length_le)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    simpa only [w, f, Q, periodicCircleJet_coe_apply, hsub,
      ContinuousMap.prod_apply, norm_prod] using hc'
  have hprod (c : OrderedFinpartition s) :
      (eLpNorm (Q c) 2 AddCircle.haarAddCircle).toReal ≤
        (c.length : ℝ) * R ^ (c.length - 1) *
          circleRealSobolevNorm (s : ℝ) (f 0) := by
    have h := circle_real_repeated_derivative_product_le f
      (periodicCircleJet_hasDerivAt v hp hv) (c.length_pos hs) c.partSize
      (oneHighPartition_sum_orders c).le hR
    have he : (∏ j : Fin c.length, (f (c.partSize j) : AddCircle P → ℝ)) =
        (Q c : AddCircle P → ℝ) := by
      funext θ
      simp only [Q, Finset.prod_apply, ContinuousMap.prod_apply]
    rw [he] at h
    exact h
  have hD := oneHigh_l2_finite_domination
    (μ := AddCircle.haarAddCircle) (g := (w s : AddCircle P → ℝ))
    (w s).continuous.aestronglyMeasurable
    (fun c : OrderedFinpartition s => (Q c : AddCircle P → ℝ))
    (fun c => ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℝ (Q c))
    (fun c => B c.length) (fun c => hB0 c.length)
    (Filter.Eventually.of_forall hpoint)
  calc
    _ ≤ ∑ c : OrderedFinpartition s, B c.length *
        (eLpNorm (Q c) 2 AddCircle.haarAddCircle).toReal := hD.2
    _ ≤ ∑ c : OrderedFinpartition s, B c.length *
        ((c.length : ℝ) * R ^ (c.length - 1) *
          circleRealSobolevNorm (s : ℝ) (f 0)) :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hprod c) (hB0 c.length)
    _ = _ := by
      simp only [circleScalarCompositionCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- A uniform constant, including order zero. Only the first through the
`max 1 s`-th outer derivatives occur. -/
def circleScalarCompositionConstant (s : ℕ) (R : ℝ) (B : ℕ → ℝ) : ℝ :=
  if s = 0 then B 1 else
    (2 : ℝ) ^ s * (B 1 + circleScalarCompositionCoefficient s R B)

/-- The complete scalar smooth-composition estimate, with the indispensable
base-point region made explicit. `R` and `B` are prescribed bounds, so this
is uniform over the input and the outer function. -/
theorem circle_scalar_composition_sobolev_le
    (s : ℕ) (v Φ : ℝ → ℝ) (hp : Periodic v P) (hv : ContDiff ℝ ∞ v)
    {S : Set ℝ} (hS : Convex ℝ S) (h0 : (0 : ℝ) ∈ S)
    (hvin : ∀ x, v x ∈ S) (hΦ : ∀ z ∈ S, ContDiffAt ℝ ∞ Φ z)
    {R : ℝ} {B : ℕ → ℝ} (hB0 : ∀ m, 0 ≤ B m)
    (hB : ∀ z ∈ S, ∀ m, 1 ≤ m → m ≤ max 1 s →
      ‖iteratedDeriv m Φ z‖ ≤ B m)
    (hR : circleRealFourierL1Norm (periodicCircleJet v hp hv 0) ≤ R) :
    circleRealSobolevNorm (s : ℝ)
      (periodicCircleJet (fun x => Φ (v x) - Φ 0)
        (periodic_sub_base_comp hp Φ)
        (contDiff_sub_base_comp hv (fun x => hΦ (v x) (hvin x))) 0) ≤
      circleScalarCompositionConstant s R B *
        circleRealSobolevNorm (s : ℝ) (periodicCircleJet v hp hv 0) := by
  let hΦv := fun x => hΦ (v x) (hvin x)
  let f := periodicCircleJet v hp hv
  let w := periodicCircleJet (fun x => Φ (v x) - Φ 0)
    (periodic_sub_base_comp hp Φ) (contDiff_sub_base_comp hv hΦv)
  have hdiff (z : ℝ) (hz : z ∈ S) : DifferentiableAt ℝ Φ z :=
    (hΦ z hz).differentiableAt (by simp)
  have hfirst (z : ℝ) (hz : z ∈ S) : ‖fderiv ℝ Φ z‖ ≤ B 1 := by
    rw [← norm_iteratedFDeriv_one Φ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hB z hz 1 le_rfl (le_max_left _ _)
  have hrange (θ : AddCircle P) : f 0 θ ∈ S := by
    refine QuotientAddGroup.induction_on θ ?_
    intro x
    simpa only [f, periodicCircleJet_coe_apply, iteratedDeriv_zero] using hvin x
  have hw0 : ⇑(w 0) = fun θ => Φ (f 0 θ) - Φ 0 := by
    funext θ
    refine QuotientAddGroup.induction_on θ ?_
    intro x
    simp only [w, f, periodicCircleJet_coe_apply, iteratedDeriv_zero]
  have hbase : (eLpNorm (w 0) 2 AddCircle.haarAddCircle).toReal ≤
      B 1 * (eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal := by
    rw [hw0]
    exact composition_sub_base_LpNorm_le hS h0 (hB0 1) hdiff hfirst
      (f 0).continuous hrange
      (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℝ (f 0))
  have hbase' : (eLpNorm (w 0) 2 AddCircle.haarAddCircle).toReal ≤
      B 1 * circleRealSobolevNorm (s : ℝ) (f 0) :=
    hbase.trans (mul_le_mul_of_nonneg_left
      (circle_real_derivative_l2_le_sobolev f (periodicCircleJet_hasDerivAt v hp hv)
        (Nat.zero_le s)) (hB0 1))
  by_cases hs : s = 0
  · subst s
    simpa [circleScalarCompositionConstant, circle_real_sobolevNorm_zero_eq_l2] using hbase
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    have hhigh := circle_scalar_composition_derivative_l2_le v Φ hp hv hΦv hspos hB0
      (fun x m hm hms => hB (v x) (hvin x) m hm (hms.trans (le_max_right _ _))) hR
    calc
      _ ≤ (2 : ℝ) ^ s *
          ((eLpNorm (w 0) 2 AddCircle.haarAddCircle).toReal +
            (eLpNorm (w s) 2 AddCircle.haarAddCircle).toReal) :=
        circle_real_sobolevNorm_le_derivative_endpoints w
          (periodicCircleJet_hasDerivAt _ _ _) s
      _ ≤ (2 : ℝ) ^ s * (B 1 * circleRealSobolevNorm (s : ℝ) (f 0) +
          circleScalarCompositionCoefficient s R B * circleRealSobolevNorm (s : ℝ) (f 0)) :=
        mul_le_mul_of_nonneg_left (add_le_add hbase' hhigh) (by positivity)
      _ = _ := by rw [circleScalarCompositionConstant, if_neg hs]; ring

end ContinuousFlexibility.Analysis
