module

public import ContinuousFlexibility.Radial.MatchedTerminalExternalColumns
public import ContinuousFlexibility.Radial.TerminalCapLayerL2
public import ContinuousFlexibility.Radial.R07CapPullback
public import Mathlib.Analysis.Convex.Jensen

/-!
# Actual terminal leading fields and their physical L² bounds

A nonnegative scalar potential controls the absolute value of the same
physical solution by its two boundary values: its square is convex.
The actual radial pullback supplies that equation. The regional leading
vector is then estimated on its original physical cap, using the actual
density and the actual weight only on that cap.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open ContinuousFlexibility.Statements
open scoped ENNReal ContDiff

/-- This single interval argument covers either placement of the unit
boundary value, and permits the potential to vanish at a turning point. -/
theorem terminalCap_solution_abs_bound {a b H : ℝ} {u du q : ℝ → ℝ}
    (hH : 0 ≤ H) (hc : ContinuousOn u (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo a b, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioo a b, 0 ≤ q x)
    (ha : |u a| ≤ H) (hb : |u b| ≤ H) :
    ∀ x ∈ Icc a b, |u x| ≤ H := by
  have hd (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun y => u y ^ 2) (2 * u x * du x) x := by
    convert (hu x hx).fun_mul (hu x hx) using 1 <;> ring
  have hdd (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun y => 2 * u y * du y)
        (2 * du x ^ 2 + 2 * q x * u x ^ 2) x := by
    convert ((hu x hx).const_mul 2).mul (hdu x hx) using 1 <;> ring
  have hconv : ConvexOn ℝ (Icc a b) (fun x => u x ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b) (hc.pow 2)
      (f' := fun x => 2 * u x * du x)
      (f'' := fun x => 2 * du x ^ 2 + 2 * q x * u x ^ 2)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hdd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) (hq x hx)) (sq_nonneg _))
  intro x hx
  have haa : u a ^ 2 ≤ H ^ 2 := by nlinarith [sq_abs (u a), abs_nonneg (u a)]
  have hbb : u b ^ 2 ≤ H ^ 2 := by nlinarith [sq_abs (u b), abs_nonneg (u b)]
  have hh := (hconv.le_max_of_mem_Icc
    (show a ∈ Icc a b from ⟨le_rfl, hx.1.trans hx.2⟩)
    (show b ∈ Icc a b from ⟨hx.1.trans hx.2, le_rfl⟩) hx).trans
      (max_le haa hbb)
  nlinarith [sq_abs (u x), abs_nonneg (u x)]


/-- The actual radial equation and profile identity give the amplitude
bound. The coordinate may have either orientation. -/
theorem terminalCap_physical_amplitude_bound
    {R w u : ℝ → ℝ} {J scale L H : ℝ}
    (hL : 0 < L) (hscale : scale ≠ 0) (hH : 0 ≤ H)
    (hR : ContDiff ℝ ∞ R) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc 0 L, w (R x) = scale * deriv R x)
    (hode : ∀ x ∈ Icc 0 L, radialJacobi J w u (R x) = 0)
    (hpotential : ∀ x ∈ Ioo 0 L, 0 ≤ J * deriv (deriv R) x / R x)
    (hleft : |u (R 0)| ≤ H) (hright : |u (R L)| ≤ H) :
    ∀ x ∈ Icc 0 L, |u (R x)| ≤ H := by
  obtain ⟨hfirst, hsecond⟩ := r07_cap_pullback_system hL hscale hR hw hu hweight hode
  exact terminalCap_solution_abs_bound hH (hu.comp hR).continuous.continuousOn
    (fun x hx => hfirst x (Ioo_subset_Icc_self hx))
    (fun x hx => hsecond x (Ioo_subset_Icc_self hx))
    hpotential hleft hright

/-- A genuine finite physical cap bounds the original regional leading
vector. The hypotheses concern the cutoff, the stand-in and the density,
rather than a norm of the vector to be estimated. -/
theorem terminalCapInnerLift_norm_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D)
    {l h a b lam P H : ℝ} {χ u : ℝ → ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hcap : Icc a b ⊆ Icc l h)
    (hcover : ∀ x ∈ Icc l h, χ x ≠ 0 → x ∈ Icc a b)
    (hcutoff : ∀ x ∈ Icc a b, |χ x| ≤ 1)
    (hvalue : ∀ x ∈ Icc a b, |u x| ≤ H)
    (hρ : ∀ x ∈ Icc a b, 12 * D.w x / x ^ 2 ≤ P) :
    ‖terminalCapInnerLift hD l h lam hχ hu‖ ≤
      (H / sqrt lam) * sqrt (P * (b - a)) := by
  let ell := modeInnerExtension l h (terminalCapLift lam χ u)
  have hsupp : Function.support ell ⊆ Icc a b := by
    intro x hx
    by_cases hi : x ∈ Icc l h
    · apply hcover x hi
      intro hz
      apply hx
      rw [show ell x = terminalCapLift lam χ u x from
        modeInnerExtension_eqOn l h _ hi]
      simp only [terminalCapLift, hz, zero_mul, zero_div]
    · exact False.elim (hx (Set.indicator_of_notMem hi _))
  have hc : ContinuousOn ell (Icc a b) :=
    (terminalCapInnerLift_representative_smooth l h lam hχ hu).continuousOn.mono hcap
  have hb : ∀ x ∈ Icc a b, |ell x| ≤ H / sqrt lam := by
    intro x hx
    rw [show ell x = terminalCapLift lam χ u x from
      modeInnerExtension_eqOn l h _ (hcap hx)]
    simp only [terminalCapLift, abs_div, abs_mul, abs_of_nonneg (sqrt_nonneg lam)]
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg lam)
    calc
      |χ x| * |u x| ≤ 1 * H :=
        mul_le_mul (hcutoff x hx) (hvalue x hx) (abs_nonneg _) (by norm_num)
      _ = H := one_mul H
  have he := (terminalCapLayer_memLp_eLpNorm D hab hP
    (div_nonneg hH (sqrt_nonneg lam)) ell hc hsupp hρ hb).2
  have hn : ‖(terminalCapInnerLift hD l h lam hχ hu).1‖ ≤
      (H / sqrt lam) * sqrt (P * (b - a)) := by
    rw [Lp.norm_def, eLpNorm_congr_ae (terminalCapInnerLift_ae hD l h lam hχ hu)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hz : (terminalCapInnerLift hD l h lam hχ hu).2 = 0 := rfl
  rw [Prod.norm_def, hz, norm_zero, max_eq_left (norm_nonneg _)]
  exact hn

/-- An almost-everywhere cap bound respects the original half-open
weight partition, including its null outer endpoints. -/
theorem matchedMode_weighted_zeroScalar_support_bound_ae {D : ReferenceData}
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (weight : ℝ → ℝ)
    (hE : ∀ f, E f =ᵐ[radialHilbertMeasure D] fun x => weight x * f x)
    (F : RadialModePair D) (hFs : F.2 = 0) (s : Set ℝ)
    (hf : ∀ᵐ x ∂radialHilbertMeasure D, x ∉ s → F.1 x = 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ᵐ x ∂radialHilbertMeasure D, x ∈ s → |weight x| ≤ A) :
    ‖(E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)) F‖ ≤ A * ‖F‖ := by
  rw [ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    hFs, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  have hn : ‖E F.1‖ ≤ A * ‖F.1‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hE F.1, hf, hlocal] with x he hz hb
    rw [he, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    by_cases hx : x ∈ s
    · exact mul_le_mul_of_nonneg_right (hb hx) (abs_nonneg _)
    · rw [hz hx, abs_zero, mul_zero, mul_zero]
  exact hn.trans (mul_le_mul_of_nonneg_left (norm_fst_le F) hA)

/-- An actual field weight pays only its bound on the original physical
cap. The leading norm itself has been derived above. -/
theorem terminalCapInnerLift_weighted_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D)
    {l h a b lam P H A : ℝ} {χ u : ℝ → ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hcap : Icc a b ⊆ Icc l h)
    (hcover : ∀ x ∈ Icc l h, χ x ≠ 0 → x ∈ Icc a b)
    (hcutoff : ∀ x ∈ Icc a b, |χ x| ≤ 1)
    (hvalue : ∀ x ∈ Icc a b, |u x| ≤ H)
    (hρ : ∀ x ∈ Icc a b, 12 * D.w x / x ^ 2 ≤ P)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (weight : ℝ → ℝ)
    (hE : ∀ f, E f =ᵐ[radialHilbertMeasure D] fun r => weight r * f r)
    (hA : 0 ≤ A)
    (hlocal : ∀ᵐ x ∂radialHilbertMeasure D, x ∈ Icc a b → |weight x| ≤ A) :
    ‖(E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
      (terminalCapInnerLift hD l h lam hχ hu)‖ ≤
        A * ((H / sqrt lam) * sqrt (P * (b - a))) := by
  let F := terminalCapInnerLift hD l h lam hχ hu
  have hz : F.2 = 0 := rfl
  have hsupp : ∀ᵐ x ∂radialHilbertMeasure D, x ∉ Icc a b → F.1 x = 0 := by
    filter_upwards [terminalCapInnerLift_ae hD l h lam hχ hu] with x hx hout
    rw [hx]
    by_cases hi : x ∈ Icc l h
    · rw [modeInnerExtension_eqOn l h _ hi]
      have hχ₀ : χ x = 0 := by
        by_contra hn
        exact hout (hcover x hi hn)
      simp only [terminalCapLift, hχ₀, zero_mul, zero_div]
    · exact Set.indicator_of_notMem hi _
  exact (matchedMode_weighted_zeroScalar_support_bound_ae E weight hE F hz (Icc a b)
    hsupp hA hlocal).trans (mul_le_mul_of_nonneg_left
      (terminalCapInnerLift_norm_bound hD hab hlam hP hH hχ hu hcap hcover
        hcutoff hvalue hρ) hA)

/-- The physical density, cap width and true boundary scale cancel both
the radial dilation and the profile height. -/
theorem terminalCap_leading_normalization {A j s k lam a d : ℝ}
    (hA : 0 < A) (hj : 0 < j) (hs : 0 < s) (hk : 0 < k)
    (ha : s / 2 ≤ a) (hd : 0 ≤ d) (hdhi : d ≤ 2 * s)
    (hlam : j ^ 2 * k * A ^ 5 / 200 ≤ lam) :
    (1 / Real.sqrt lam) * Real.sqrt ((12 * (7 * k * s * A) / a ^ 2) * d) ≤
      400 / (j * A ^ 2) := by
  have ha₀ : 0 < a := (by positivity : 0 < s / 2).trans_le ha
  have hl₀ : 0 < lam := (by positivity : 0 < j ^ 2 * k * A ^ 5 / 200).trans_le hlam
  have hm₀ : 0 ≤ (12 * (7 * k * s * A) / a ^ 2) * d := by positivity
  have hmass : (12 * (7 * k * s * A) / a ^ 2) * d ≤ 672 * k * A := by
    calc
      _ ≤ (12 * (7 * k * s * A) / (s / 2) ^ 2) * (2 * s) :=
        mul_le_mul
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            ((sq_le_sq₀ (by positivity) ha₀.le).mpr ha))
          hdhi hd (by positivity)
      _ = 672 * k * A := by field_simp [hs.ne']; ring
  have hh : Real.sqrt ((12 * (7 * k * s * A) / a ^ 2) * d) ≤
      (400 / (j * A ^ 2)) * Real.sqrt lam := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hm₀, Real.sq_sqrt hl₀.le]
    calc
      _ ≤ 672 * k * A := hmass
      _ ≤ 800 * k * A := by nlinarith [mul_pos hk hA]
      _ = (400 / (j * A ^ 2)) ^ 2 * (j ^ 2 * k * A ^ 5 / 200) := by
        field_simp [hj.ne', hA.ne']
        ring
      _ ≤ (400 / (j * A ^ 2)) ^ 2 * lam :=
        mul_le_mul_of_nonneg_left hlam (sq_nonneg _)
  have hdiv := (div_le_iff₀ (Real.sqrt_pos.mpr hl₀)).mpr hh
  convert hdiv using 1 <;> ring

end ContinuousFlexibility.Radial
