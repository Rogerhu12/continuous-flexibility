import ContinuousFlexibility.Analysis.N01PositiveProfileNeighborhood
import ContinuousFlexibility.Analysis.N01RootRadialCoefficientValues
import ContinuousFlexibility.Analysis.N01CoefficientValueJets
import ContinuousFlexibility.Analysis.LocalMixedProductBounds

/-!
# Actual finite inputs at every regular positive endpoint

One state order and one radius are selected before the endpoint. The
actual N01 coefficient difference bound then controls all three original
coefficients through total order three on that endpoint circle. The
reference terms are a finite collection of real numbers, since the
reference coefficients are radial.

The same radius keeps the scalar metric parameter in a closed subinterval
of the common positive-profile parameter interval. A true minimum there
gives a determinant lower bound independent of the state and angle.
These are inputs for the finite degree-three conformal construction,
not estimates for a chart, an inverse, or a canonical field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem positiveInput_mem_cell
    {D : ReferenceData} (hP : RadialPartition D) {r : ℝ}
    (hr : r ∈ radialCore D) : ∃ m, r ∈ D.cells m := by
  by_contra! hnone
  have hz (m : ℕ) : D.localizer m r = 0 := by
    by_contra hm
    exact hnone m (hP.2.2.1 m (Function.mem_support.mpr hm))
  have he := (hP.2.2.2.2.1 r hr).2
  have hzero : (0 : ℝ) = 1 := by simpa only [hz, tsum_zero] using he
  exact zero_ne_one hzero

private theorem positiveInput_reference_angle
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (i : Fin 3) (a b : ℕ) (r θ : ℝ) :
    mixedDerivative a b
        (canonicalCoefficientComponent i (originalCoefficients D S C (C.referenceState, 0)))
        (r, θ) =
      mixedDerivative a b
        (canonicalCoefficientComponent i (originalCoefficients D S C (C.referenceState, 0)))
        (r, 0) := by
  have he (x : ℝ) :
      (fun η => canonicalCoefficientComponent i
        (originalCoefficients D S C (C.referenceState, 0)) (x, η)) =
      fun _ : ℝ => canonicalCoefficientComponent i
        (originalCoefficients D S C (C.referenceState, 0)) (x, 0) :=
    funext fun η => originalCoefficientComponent_zeroParameter_angle_invariant
      D S C C.referenceState i x η 0
  unfold mixedDerivative
  simp_rw [he]
  simp only [iteratedDeriv_const]

private theorem positiveInput_reference_bound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ 3 → ∀ θ,
      |mixedDerivative a b
        (canonicalCoefficientComponent i (originalCoefficients D S C (C.referenceState, 0)))
        (r, θ)| ≤ M := by
  let R : Fin 3 × Fin 4 × Fin 4 → ℝ := fun j =>
    mixedDerivative j.2.1 j.2.2
      (canonicalCoefficientComponent j.1 (originalCoefficients D S C (C.referenceState, 0)))
      (r, 0)
  refine ⟨∑ j, |R j|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro i a b hab θ
  have ha : a < 4 := by omega
  have hb : b < 4 := by omega
  rw [positiveInput_reference_angle]
  exact Finset.single_le_sum (f := fun j => |R j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (i, (⟨a, ha⟩ : Fin 4), (⟨b, hb⟩ : Fin 4)))

private theorem positiveInput_pair_le_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {k base : ℕ} (hk : k ≤ base) {ε : ℝ} (hε : ε ≤ 1 / 2)
    {x : E} {z : E × ℝ} (hz : p base (z.1 - x) < ε) (hq : |z.2| < ε) :
    pairGrading p realGrading k (z - (x, 0)) ≤ 1 := by
  simp only [pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Prod.fst_sub, Prod.snd_sub, sub_zero,
    realGrading, coe_normSeminorm, Real.norm_eq_abs]
  have hs := hp hk (z.1 - x)
  linarith

private theorem positiveInput_abs_bound
    {x y W M t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1)
    (hdiff : |x - y| ≤ W * (1 + t)) (href : |y| ≤ M) :
    |x| ≤ 1 + 2 * |W| + M := by
  have hdiff' : |x - y| ≤ 2 * |W| :=
    hdiff.trans ((mul_le_mul_of_nonneg_right (le_abs_self W) (by linarith)).trans
      (by nlinarith [abs_nonneg W]))
  have he : x = (x - y) + y := by ring
  calc
    |x| = |(x - y) + y| := congrArg abs he
    _ ≤ |x - y| + |y| := abs_add_le _ _
    _ ≤ 1 + 2 * |W| + M := by linarith

/-- The full finite-order body is named before the numerical constant is
chosen, so the concrete projective state is not unfolded during choice. -/
def N01PositiveCircleMixedJets
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε r M : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ,
    ∀ i : Fin 3, ∀ a b : ℕ, a + b ≤ 3 →
      |mixedDerivative a b
        (canonicalCoefficientComponent i (originalCoefficients D S C z)) (r, θ)| ≤ M

private theorem positiveInput_mixedJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss base' : ℕ} {ε ε' r : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (horder : 3 + loss ≤ base')
    (hε : ε' ≤ ε) (hεhalf : ε' ≤ 1 / 2) (hr : r ∈ radialCore D) :
    ∃ M : ℝ, 0 < M ∧ N01PositiveCircleMixedJets D S C base' ε' r M := by
  obtain ⟨_, hD⟩ := hN.1.1
  obtain ⟨m, hm⟩ := positiveInput_mem_cell hD.2.1 hr
  obtain ⟨R, hR, href⟩ := positiveInput_reference_bound D S C r
  obtain ⟨B, _hB, hbound⟩ := coefficientFamily_value_bound_of_n01 hN 3
  let W : ℝ := B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B
  refine ⟨1 + 2 * |W| + R, by positivity, ?_⟩
  intro z hz hs θ i a b hab
  have hz₀ := stateNeighborhood_mono S C hb hε hz
  have hp := positiveInput_pair_le_one (stateGrading_monotone S) horder
    hεhalf hz.1 hz.2
  have hcurrent := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz₀ hs i
  have hreference := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN
    (reference_mem_stateNeighborhood S C base hN.2.1) hN.2.2.1.stateSector i
  have hsub := mixedDerivative_sub_of_contDiffOn
    (isOpen_Ioo.prod isOpen_univ) hcurrent hreference a b
    (p := (r, θ)) ⟨hr, mem_univ _⟩
  have he : coefficientFamily D S C i a b (r, θ) z =
      mixedDerivative a b (canonicalCoefficientComponent i (originalCoefficients D S C z)) (r, θ) -
        mixedDerivative a b (canonicalCoefficientComponent i
          (originalCoefficients D S C (C.referenceState, 0))) (r, θ) := by
    calc
      _ = mixedDerivative a b (fun q =>
          canonicalCoefficientComponent i (originalCoefficients D S C z) q -
            canonicalCoefficientComponent i
              (originalCoefficients D S C (C.referenceState, 0)) q) (r, θ) := by
        unfold coefficientFamily canonicalCoefficientComponent
        split_ifs <;> rfl
      _ = _ := hsub
  have hdiff := (congrArg abs he).symm.trans_le
    (hbound m i a b (r, θ) hab hm z hz₀)
  exact positiveInput_abs_bound (apply_nonneg _ _) hp hdiff (href i a b hab θ)

private theorem positiveInput_metricSlope_lower
    {w χ : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    {η r : ℝ} (hη : 0 < η) (hr : 0 < deriv w r)
    (hpositive : ∀ ν : ℝ, |ν| < η → ∀ s : ℝ, 0 < deriv w s →
      0 < deriv (fun t => w t * Real.exp (ν * χ t)) s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ν : ℝ, |ν| ≤ η / 2 →
      κ ≤ deriv (fun t => w t * Real.exp (ν * χ t)) r := by
  let f : ℝ → ℝ := fun ν =>
    Real.exp (ν * χ r) * (deriv w r + ν * w r * deriv χ r)
  have hf : Continuous f :=
    (continuous_id.mul continuous_const).exp.mul
      (continuous_const.add ((continuous_id.mul continuous_const).mul continuous_const))
  have he (ν : ℝ) : f ν = deriv (fun t => w t * Real.exp (ν * χ t)) r := by
    have hd := ((hw.differentiable (by simp) r).hasDerivAt.fun_mul
      (((hχ.differentiable (by simp) r).hasDerivAt.const_mul ν).exp)).deriv
    rw [hd]
    dsimp only [f]
    ring
  obtain ⟨ν₀, hν₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by linarith : -(η / 2) ≤ η / 2)) hf.continuousOn
  refine ⟨f ν₀, ?_, ?_⟩
  · rw [he]
    exact hpositive ν₀ (abs_lt.mpr ⟨by linarith [hν₀.1], by linarith [hν₀.2]⟩) r hr
  · intro ν hν
    rw [← he]
    exact hmin (abs_le.mp hν)

private theorem positiveInput_det_lower
    {wref w dw κ r Q : ℝ} (hwref : 0 < wref) (hκ : 0 < κ) (hr : 0 < r)
    (hw : (1 / 2 : ℝ) ≤ w / wref) (hdw : κ ≤ dw)
    (hQl : (1 / 2 : ℝ) ≤ Q) (hQu : Q ≤ (3 / 2 : ℝ)) :
    wref * κ / (8 * r) ≤ (w * dw / r) / Q ^ 2 := by
  have hwl : wref / 2 ≤ w := by
    have h := (le_div_iff₀ hwref).mp hw
    linarith
  have hwp : 0 < w := (half_pos hwref).trans_le hwl
  have hdwp : 0 < dw := hκ.trans_le hdw
  have hm := mul_le_mul hwl hdw hκ.le hwp.le
  have hd := div_le_div_of_nonneg_right hm hr.le
  have hsq := (root_positive_square_denominator_bounds
    (div_nonneg (mul_nonneg hwp.le hdwp.le) hr.le) hQl hQu).1
  calc
    wref * κ / (8 * r) = ((wref / 2 * κ) / r) / 4 := by field_simp [hr.ne'] <;> ring
    _ ≤ (w * dw / r) / 4 := div_le_div_of_nonneg_right hd (by norm_num)
    _ ≤ _ := hsq

/-- Actual positive endpoint values on the original common state grading.
The determinant lower bound is chosen before the state and angle. -/
def N01PositiveCircleValues
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε r κ : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ,
    0 < deriv (stateProfile D S C z.1) r ∧
      (originalCoefficients D S C z).a (r, θ) ∈ Icc (D.w r / 8) (16 * D.w r) ∧
      κ ≤ (originalCoefficients D S C z).a (r, θ) *
        (originalCoefficients D S C z).c (r, θ) -
          (originalCoefficients D S C z).b (r, θ) ^ 2

/-- One neighborhood supplies genuine regular positive endpoint inputs
for every future buffered piece. The maximum derivative order is the
fixed number three; no final canonical bound is an input. -/
theorem n01_exists_positiveCircle_finite_inputs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ r ∈ radialCore D, 0 < deriv D.w r → ∃ κ M : ℝ, 0 < κ ∧ 0 < M ∧
        N01PositiveCircleValues D S C base' ε' r κ ∧
        N01PositiveCircleMixedJets D S C base' ε' r M := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hborder : RadialTrueBorder D := hN.1.2.2.2.1
  obtain ⟨η, hη, hpositive⟩ := exists_logProfile_positive_parameter hw hborder.1
    hborder.2.1 (fun r hr => (hborder.2.2.1 hr).2)
  let base' := max base (3 + loss)
  let ε' := min ε (min (η / 2) (1 / 2))
  have hε' : 0 < ε' := lt_min hN.2.1 (lt_min (half_pos hη) (by norm_num))
  have hεold : ε' ≤ ε := min_le_left _ _
  have hεη : ε' ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεhalf : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨base', ε', le_max_left _ _, hε', hεold, ?_⟩
  intro r hr hrpos
  have hr₀ : 0 < r := hD.1.1.trans hr.1
  have hwref : 0 < D.w r := hD.1.2.2.2.2.1 r hr
  obtain ⟨κ₀, hκ₀, hκbound⟩ := positiveInput_metricSlope_lower hw hborder.1 hη hrpos hpositive
  obtain ⟨M, hM, hjets⟩ := positiveInput_mixedJets hS hT hN
    (le_max_left _ _) (le_max_right _ _) hεold hεhalf hr
  refine ⟨D.w r * κ₀ / (8 * r), M, by positivity, hM, ?_, hjets⟩
  intro z hz hs θ
  have hz₀ := stateNeighborhood_mono S C (le_max_left base (3 + loss)) hεold hz
  have hν : |z.1.2.1| ≤ η / 2 :=
    ((stateMetricCoordinate_abs_le_stateGrading S hN.2.2.1.2.2.1 base' z.1).trans_lt
      hz.1).le.trans hεη
  have he := stateProfile_eventuallyEq_metric_on_positive hN.2.2.2.1
    (contDiff_infty_iff_deriv.mp hw).2.continuous z.1 hrpos
  have hder : κ₀ ≤ deriv (stateProfile D S C z.1) r := by
    rw [he.deriv_eq]
    exact hκbound z.1.2.1 hν
  have ha := n01_scaledRadialCoefficient_root_values (σ := 1)
    hN hr (by norm_num : (0 : ℝ) < 1) hz₀ hs θ
  have ha' : (originalCoefficients D S C z).a (r, θ) ∈
      Icc (D.w r / 8) (16 * D.w r) := by
    simpa only [rootScaledRadialCoefficient, mul_zero, add_zero, div_one, mul_one] using ha
  have hnum := hN.2.2.2.2.2.2.2.2.2.1 z hz₀ hs (r, θ) ⟨hr, mem_univ _⟩
  have hwp : 0 < stateProfile D S C z.1 r := by
    change 0 < D.w r * Real.exp _
    exact mul_pos hwref (Real.exp_pos _)
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) (r, θ))
      (heightRadial (stateHeight D S C z) (r, θ))
      (angularPartial (heightAngular (stateHeight D S C z)) (r, θ)) :=
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hwp).trans_le
      ((le_div_iff₀ hwp).mp hnum.2.2.1)
  have hDisc : 0 < polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) (r, θ) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hnum.2.2.2.2.1
  have hdet := polar_corrected_determinant (stateHeight D S C z)
    ((contDiff_stateProfile_of_n01 hS hT hN z.1).differentiable (by simp) r)
    hr₀.ne' hDisc hQ.ne'
  refine ⟨hκ₀.trans_le hder, ha', ?_⟩
  exact (positiveInput_det_lower hwref hκ₀ hr₀ hnum.1 hder
    hnum.2.2.2.2.1 hnum.2.2.2.2.2).trans_eq hdet.symm

end ContinuousFlexibility.Analysis

