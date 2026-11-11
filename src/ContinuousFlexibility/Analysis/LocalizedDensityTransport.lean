import ContinuousFlexibility.Analysis.L2BoundedMultiplier
import ContinuousFlexibility.Analysis.SquareDensityIsometry

/-!
# Localized inverse kernels under a change of density

An unweighted localized inverse is obtained from its weighted localized
kernel by the two reciprocal square-root density multipliers. The theorem
uses bounds only on those localized multipliers. No global reciprocal
density bound is asserted or required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable (μ : Measure ℝ) {a bk bm : ℝ → ℝ} {Mk Mm : ℝ}
  (ha : Measurable a) (hpos : ∀ x, 0 < a x)
  (hk : AEStronglyMeasurable bk μ) (hm : AEStronglyMeasurable bm μ)
  (hkb : ∀ᵐ x ∂μ, |bk x| ≤ Mk) (hmb : ∀ᵐ x ∂μ, |bm x| ≤ Mm)

/-- The actual unweighted localized operator, with both density factors. -/
def localizedDensityInverse
    (R : Lp ℝ 2 (squareDensityMeasure μ a) →L[ℝ] Lp ℝ 2 (squareDensityMeasure μ a)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  -(l2BoundedMultiplier μ hk hkb).comp
    ((squareDensityEquiv μ ha hpos).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (R.comp ((squareDensityEquiv μ ha hpos).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (l2BoundedMultiplier μ hm hmb))))

theorem norm_localizedDensityInverse_le
    (R : Lp ℝ 2 (squareDensityMeasure μ a) →L[ℝ] Lp ℝ 2 (squareDensityMeasure μ a))
    {B : ℝ} (hMk : 0 ≤ Mk) (hMm : 0 ≤ Mm) (hB : 0 ≤ B) (hR : ‖R‖ ≤ B) :
    ‖localizedDensityInverse μ ha hpos hk hm hkb hmb R‖ ≤ Mk * B * Mm := by
  let E := squareDensityEquiv μ ha hpos
  let K := l2BoundedMultiplier μ hk hkb
  let M := l2BoundedMultiplier μ hm hmb
  have hk' (f : Lp ℝ 2 μ) : ‖K f‖ ≤ Mk * ‖f‖ :=
    (K.le_opNorm f).trans (mul_le_mul_of_nonneg_right
      (norm_l2BoundedMultiplier_le μ hk hMk hkb) (norm_nonneg _))
  have hm' (f : Lp ℝ 2 μ) : ‖M f‖ ≤ Mm * ‖f‖ :=
    (M.le_opNorm f).trans (mul_le_mul_of_nonneg_right
      (norm_l2BoundedMultiplier_le μ hm hMm hmb) (norm_nonneg _))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖-K (E (R (E.symm (M f))))‖ ≤ _
  rw [norm_neg]
  calc
    _ ≤ Mk * ‖E (R (E.symm (M f)))‖ := hk' _
    _ = Mk * ‖R (E.symm (M f))‖ := by rw [E.norm_map]
    _ ≤ Mk * (B * ‖E.symm (M f)‖) := mul_le_mul_of_nonneg_left
      ((R.le_opNorm _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) hMk
    _ = Mk * (B * ‖M f‖) := by rw [E.symm.norm_map]
    _ ≤ Mk * (B * (Mm * ‖f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hm' f) hB) hMk
    _ = (Mk * B * Mm) * ‖f‖ := by ring

/-- If the weighted localized inverse has kernel K and the multipliers
are the reciprocal density on its two supports, the constructed operator
has exactly the same kernel with a minus sign and unweighted integration. -/
theorem localizedDensityInverse_kernel
    (R : Lp ℝ 2 (squareDensityMeasure μ a) →L[ℝ] Lp ℝ 2 (squareDensityMeasure μ a))
    (K : ℝ → ℝ → ℝ)
    (hR : ∀ f : Lp ℝ 2 (squareDensityMeasure μ a),
      (R f : ℝ → ℝ) =ᵐ[squareDensityMeasure μ a] fun x =>
        ∫ y, K x y * f y ∂squareDensityMeasure μ a)
    (hleft : ∀ x y, bk x * a x * K x y = K x y)
    (hright : ∀ x y, a y * bm y * K x y = K x y)
    (f : Lp ℝ 2 μ) :
    (localizedDensityInverse μ ha hpos hk hm hkb hmb R f : ℝ → ℝ) =ᵐ[μ]
      fun x => -(∫ y, K x y * f y ∂μ) := by
  let E := squareDensityEquiv μ ha hpos
  let M := l2BoundedMultiplier μ hm hmb
  let B := l2BoundedMultiplier μ hk hkb
  let q := E.symm (M f)
  have hq : (q : ℝ → ℝ) =ᵐ[μ] fun y => bm y * f y / a y := by
    filter_upwards [squareDensityEquiv_symm_ae μ ha hpos (M f),
      l2BoundedMultiplier_ae μ hm hmb f] with y hy hf
    exact hy.trans (congrArg (fun t => t / a y) hf)
  have hq' : (q : ℝ → ℝ) =ᵐ[squareDensityMeasure μ a]
      fun y => bm y * f y / a y :=
    (withDensity_absolutelyContinuous μ _).ae_eq hq
  have hrow (x : ℝ) :
      (∫ y, K x y * q y ∂squareDensityMeasure μ a) = ∫ y, K x y * f y ∂μ := by
    calc
      _ = ∫ y, K x y * (bm y * f y / a y) ∂squareDensityMeasure μ a := by
        apply integral_congr_ae
        filter_upwards [hq'] with y hy
        rw [hy]
      _ = ∫ y, a y ^ 2 * (K x y * (bm y * f y / a y)) ∂μ := by
        rw [squareDensityMeasure, integral_withDensity_eq_integral_toReal_smul
          (ha.pow_const 2).ennreal_ofReal (by simp)]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => by
          dsimp only
          rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul])
      _ = _ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro y
        calc
          a y ^ 2 * (K x y * (bm y * f y / a y)) =
              (a y * bm y * K x y) * f y := by field_simp [(hpos y).ne'] <;> ring
          _ = K x y * f y := by rw [hright]
  have hRi := squareDensity_ae_eq μ ha hpos (hR q)
  have hE := squareDensityEquiv_ae μ ha hpos (R q)
  have hB := l2BoundedMultiplier_ae μ hk hkb (E (R q))
  have hneg := Lp.coeFn_neg (B (E (R q)))
  filter_upwards [hRi, hE, hB, hneg] with x hri he hb hn
  change (-(B (E (R q))) : Lp ℝ 2 μ) x = _
  rw [hn]
  change -(B (E (R q)) x) = _
  rw [hb, he, hri, hrow]
  congr 1
  calc
    bk x * (a x * ∫ y, K x y * f y ∂μ) =
        ∫ y, (bk x * a x) * (K x y * f y) ∂μ := by
      rw [integral_const_mul]
      ring
    _ = ∫ y, K x y * f y ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        calc
          (bk x * a x) * (K x y * f y) = (bk x * a x * K x y) * f y := by ring
          _ = K x y * f y := by rw [hleft])

end ContinuousFlexibility.Analysis
