import ContinuousFlexibility.Analysis.OneHighCircleFourierChangeVariables
import ContinuousFlexibility.Analysis.OneHighCircleRealSobolev
import ContinuousFlexibility.Analysis.OneHighCompositionJets
import Mathlib.Topology.ContinuousMap.Lattice

/-!
# Low-order circle composition estimates

The actual Faà di Bruno formula is combined with change of variables. Bounds
on the first three derivatives of the lift will provide the uniform low-order
base for the tame high-order induction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Function
open scoped ENNReal BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every ordinary derivative of a smooth function is again smooth. -/
theorem circle_contDiff_iteratedDeriv {v : ℝ → E} (hv : ContDiff ℝ ∞ v) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n v) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hv

/-- A bound on the inner derivatives yields an actual pointwise
composition bound, with all outer derivative orders retained. -/
theorem circleLift_norm_iteratedDeriv_comp_le {u : ℝ → E} {h : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h) (s : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ j : ℕ, 1 ≤ j → j ≤ s → ∀ x : ℝ, ‖iteratedDeriv j h x‖ ≤ B)
    (x : ℝ) :
    ‖iteratedDeriv s (u ∘ h) x‖ ≤
      ∑ q : OrderedFinpartition s, B ^ q.length * ‖iteratedDeriv q.length u (h x)‖ := by
  classical
  have hchain := norm_iteratedFDeriv_comp_le_partition_sum
    (x := x) hu.contDiffAt hh.contDiffAt s
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hchain
  apply hchain.trans
  apply Finset.sum_le_sum
  intro q _
  have hp : (∏ j, ‖iteratedDeriv (q.partSize j) h x‖) ≤ B ^ q.length := by
    calc
      _ ≤ ∏ _j : Fin q.length, B := Finset.prod_le_prod₀
        (fun _ _ => norm_nonneg _) (fun j _ =>
          hbound (q.partSize j) (q.partSize_pos j) (q.partSize_le j) x)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedDeriv q.length u (h x)))

variable {P : ℝ} [Fact (0 < P)]

/-- The zeroth circle jet of an actual derivative is the corresponding
member of the original derivative tower. -/
theorem periodicCircleJet_iteratedDeriv_zero (v : ℝ → E) (hp : Periodic v P)
    (hv : ContDiff ℝ ∞ v) (j : ℕ) :
    periodicCircleJet (iteratedDeriv j v) (periodic_iteratedDeriv hp j)
      (circle_contDiff_iteratedDeriv hv j) 0 = periodicCircleJet v hp hv j := by
  ext θ
  induction θ using QuotientAddGroup.induction_on
  simp only [periodicCircleJet_coe_apply, iteratedDeriv_zero]

/-- Absolute value preserves the actual circle `L²` norm. -/
theorem circle_l2_abs (f : C(AddCircle P, ℝ)) :
    (eLpNorm |f| 2 AddCircle.haarAddCircle).toReal =
      (eLpNorm f 2 AddCircle.haarAddCircle).toReal := by
  congr 1
  apply eLpNorm_congr_norm_ae (|f|).continuous.aestronglyMeasurable
    f.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun θ => by
    simp only [ContinuousMap.abs_apply, Real.norm_eq_abs, abs_abs]

/-- A finite pointwise weighted majorant gives the corresponding actual
circle L2 bound. Keeping this elementary step separate avoids expanding
the full periodic derivative tower during the composition proof. -/
private theorem circle_l2_le_weighted_sum {ι : Type*} [Fintype ι]
    (f : C(AddCircle P, ℝ)) (g : ι → C(AddCircle P, ℝ)) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hpoint : ∀ θ, ‖f θ‖ ≤ ∑ i, b i * ‖g i θ‖) :
    (eLpNorm f 2 AddCircle.haarAddCircle).toReal ≤
      ∑ i, b i * (eLpNorm (g i) 2 AddCircle.haarAddCircle).toReal := by
  classical
  let A : ι → C(AddCircle P, ℝ) := fun i => b i • |g i|
  have hsum (θ : AddCircle P) : 0 ≤ (∑ i, A i) θ := by
    simp only [ContinuousMap.sum_apply, A, ContinuousMap.smul_apply,
      ContinuousMap.abs_apply, smul_eq_mul]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (abs_nonneg _))
  have hdom (θ : AddCircle P) : ‖f θ‖ ≤ ‖(∑ i, A i) θ‖ := by
    rw [Real.norm_of_nonneg (hsum θ)]
    simpa only [ContinuousMap.sum_apply, A, ContinuousMap.smul_apply,
      ContinuousMap.abs_apply, smul_eq_mul, Real.norm_eq_abs] using hpoint θ
  have hterm (i : ι) : (eLpNorm (A i) 2 AddCircle.haarAddCircle).toReal =
      b i * (eLpNorm (g i) 2 AddCircle.haarAddCircle).toReal := by
    dsimp only [A]
    rw [circle_l2_const_smul _ (hb i), circle_l2_abs]
  calc
    _ ≤ (eLpNorm (∑ i, A i) 2 AddCircle.haarAddCircle).toReal :=
      circle_l2_le_of_norm_le f (∑ i, A i) hdom
    _ ≤ ∑ i, (eLpNorm (A i) 2 AddCircle.haarAddCircle).toReal := circle_l2_sum_le A
    _ = _ := Finset.sum_congr rfl (fun i _ => hterm i)

/-- An actual outer derivative, composed with the lift, is controlled by
change of variables and the original finite Sobolev norm. -/
private theorem circleLift_outerDerivative_l2_comp_le (u : ℝ → ℝ)
    (hp : Periodic u P) (hu : ContDiff ℝ ∞ u) (h : ℝ → ℝ)
    (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ deriv h x)
    (s j : ℕ) (hj : j ≤ s) :
    (eLpNorm (periodicCircleJet ((iteratedDeriv j u) ∘ h)
      (periodic_comp_circleLift (periodic_iteratedDeriv hp j) hlift)
      ((circle_contDiff_iteratedDeriv hu j).comp hh) 0)
        2 AddCircle.haarAddCircle).toReal ≤
      (Real.sqrt c)⁻¹ * circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0) := by
  have hcomp := periodicCircleJet_l2_comp_le (iteratedDeriv j u)
    (periodic_iteratedDeriv hp j) (circle_contDiff_iteratedDeriv hu j)
    h hh hlift hc hlower
  rw [periodicCircleJet_iteratedDeriv_zero u hp hu j] at hcomp
  exact hcomp.trans (mul_le_mul_of_nonneg_left
    (circle_real_derivative_l2_le_sobolev (periodicCircleJet u hp hu)
      (periodicCircleJet_hasDerivAt u hp hu) hj)
    (inv_nonneg.mpr (Real.sqrt_nonneg c)))

/-- Genuine `L²` control of an arbitrary derivative of the composition
from bounds on the inner derivatives through that same order. -/
theorem circleLift_derivative_l2_comp_le (u : ℝ → ℝ) (hp : Periodic u P)
    (hu : ContDiff ℝ ∞ u) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hlower : ∀ x, c ≤ deriv h x) (s : ℕ)
    (hbound : ∀ j : ℕ, 1 ≤ j → j ≤ s → ∀ x : ℝ, ‖iteratedDeriv j h x‖ ≤ B) :
    (eLpNorm (periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift)
        (hu.comp hh) s) 2 AddCircle.haarAddCircle).toReal ≤
      (∑ q : OrderedFinpartition s, B ^ q.length) * (Real.sqrt c)⁻¹ *
        circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0) := by
  classical
  let W : C(AddCircle P, ℝ) :=
    periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) s
  let V : OrderedFinpartition s → C(AddCircle P, ℝ) := fun q =>
    periodicCircleJet ((iteratedDeriv q.length u) ∘ h)
      (periodic_comp_circleLift (periodic_iteratedDeriv hp q.length) hlift)
      ((circle_contDiff_iteratedDeriv hu q.length).comp hh) 0
  have hpoint (θ : AddCircle P) : ‖W θ‖ ≤ ∑ q, B ^ q.length * ‖V q θ‖ := by
    induction θ using QuotientAddGroup.induction_on
    rename_i x
    simpa only [W, V, periodicCircleJet_coe_apply, iteratedDeriv_zero,
      Function.comp_apply] using circleLift_norm_iteratedDeriv_comp_le hu hh s hB hbound x
  apply (circle_l2_le_weighted_sum W V (fun q => B ^ q.length)
    (fun q => pow_nonneg hB q.length) hpoint).trans
  calc
    _ ≤ ∑ q : OrderedFinpartition s, B ^ q.length *
        ((Real.sqrt c)⁻¹ * circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0)) :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left
        (circleLift_outerDerivative_l2_comp_le u hp hu h hh hlift hc hlower
          s q.length q.length_le) (pow_nonneg hB q.length))
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

/-- The actual Sobolev composition estimate when derivatives of the lift
through order `s` have a fixed pointwise bound. For `s ≤ 3` these bounds
follow from the prescribed low `H³` norm of `h' - 1`. -/
theorem circleLift_sobolev_comp_le_of_derivative_bound (u : ℝ → ℝ)
    (hp : Periodic u P) (hu : ContDiff ℝ ∞ u) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hlower : ∀ x, c ≤ deriv h x) (s : ℕ)
    (hbound : ∀ j : ℕ, 1 ≤ j → j ≤ s → ∀ x : ℝ, ‖iteratedDeriv j h x‖ ≤ B) :
    circleRealSobolevNorm (s : ℝ)
        (periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 0) ≤
      ((2 : ℝ) ^ s * (Real.sqrt c)⁻¹ *
        (1 + ∑ q : OrderedFinpartition s, B ^ q.length)) *
        circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0) := by
  let U : ℕ → C(AddCircle P, ℝ) := periodicCircleJet u hp hu
  let W : ℕ → C(AddCircle P, ℝ) :=
    periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh)
  have hzero := (periodicCircleJet_l2_comp_le u hp hu h hh hlift hc hlower).trans
    (mul_le_mul_of_nonneg_left
      (circle_real_derivative_l2_le_sobolev U (periodicCircleJet_hasDerivAt u hp hu)
        (Nat.zero_le s)) (inv_nonneg.mpr (Real.sqrt_nonneg c)))
  have htop := circleLift_derivative_l2_comp_le u hp hu h hh hlift hc hB hlower s hbound
  calc
    _ ≤ (2 : ℝ) ^ s * ((eLpNorm (W 0) 2 AddCircle.haarAddCircle).toReal +
        (eLpNorm (W s) 2 AddCircle.haarAddCircle).toReal) :=
      circle_real_sobolevNorm_le_derivative_endpoints W
        (periodicCircleJet_hasDerivAt (u ∘ h) (periodic_comp_circleLift hp hlift)
          (hu.comp hh)) s
    _ ≤ (2 : ℝ) ^ s *
        ((Real.sqrt c)⁻¹ * circleRealSobolevNorm (s : ℝ) (U 0) +
          (∑ q : OrderedFinpartition s, B ^ q.length) * (Real.sqrt c)⁻¹ *
            circleRealSobolevNorm (s : ℝ) (U 0)) :=
      mul_le_mul_of_nonneg_left (add_le_add hzero htop) (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
