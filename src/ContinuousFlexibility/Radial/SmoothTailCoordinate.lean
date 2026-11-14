module

public import ContinuousFlexibility.Radial.ReferenceCoordinate
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# A smooth coordinate with independent linear tails

The forward map is A*r + (B-A)*r*ζ((r-c)/(d-c)), where 0<c<d
and 0<A≤B.  Its extra summand is monotone, so its derivative is
at least A.  The inverse is therefore smooth.  The transition occurs
only inside [c,d], and both coordinate directions are globally
Lipschitz.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

def radialTailRamp (c d r : ℝ) : ℝ :=
  r * Real.smoothTransition ((r - c) / (d - c))

def radialTailStretch (A B c d r : ℝ) : ℝ :=
  A * r + (B - A) * radialTailRamp c d r

theorem radialTailRamp_contDiff (c d : ℝ) :
    ContDiff ℝ ∞ (radialTailRamp c d) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (d - c)))

theorem radialTailStretch_contDiff (A B c d : ℝ) :
    ContDiff ℝ ∞ (radialTailStretch A B c d) :=
  (contDiff_const.mul contDiff_id).add
    (contDiff_const.mul (radialTailRamp_contDiff c d))

theorem radialTailRamp_left {c d r : ℝ} (hcd : c < d) (hr : r ≤ c) :
    radialTailRamp c d r = 0 := by
  have hq : (r - c) / (d - c) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) (sub_pos.mpr hcd).le
  simp only [radialTailRamp, Real.smoothTransition.zero_of_nonpos hq, mul_zero]

theorem radialTailRamp_right {c d r : ℝ} (hcd : c < d) (hr : d ≤ r) :
    radialTailRamp c d r = r := by
  have hq : 1 ≤ (r - c) / (d - c) := by
    apply (le_div_iff₀ (sub_pos.mpr hcd)).mpr
    linarith
  simp only [radialTailRamp, Real.smoothTransition.one_of_one_le hq, mul_one]

theorem radialTailStretch_left {A B c d r : ℝ} (hcd : c < d) (hr : r ≤ c) :
    radialTailStretch A B c d r = A * r := by
  rw [radialTailStretch, radialTailRamp_left hcd hr]
  ring

theorem radialTailStretch_right {A B c d r : ℝ} (hcd : c < d) (hr : d ≤ r) :
    radialTailStretch A B c d r = B * r := by
  rw [radialTailStretch, radialTailRamp_right hcd hr]
  ring

theorem radialTailRamp_monotone {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Monotone (radialTailRamp c d) := by
  intro x y hxy
  by_cases hx : x ≤ c
  · rw [radialTailRamp_left hcd hx]
    by_cases hy : y ≤ c
    · simpa only [radialTailRamp_left hcd hy] using (le_rfl : (0 : ℝ) ≤ 0)
    · exact mul_nonneg (hc.trans (lt_of_not_ge hy)).le (Real.smoothTransition.nonneg _)
  · have hx0 : 0 ≤ x := (hc.trans (lt_of_not_ge hx)).le
    have hζ : Real.smoothTransition ((x - c) / (d - c)) ≤
        Real.smoothTransition ((y - c) / (d - c)) :=
      Real.smoothTransition.monotone
        (div_le_div_of_nonneg_right (sub_le_sub_right hxy c) (sub_pos.mpr hcd).le)
    exact mul_le_mul hxy hζ (Real.smoothTransition.nonneg _) (hx0.trans hxy)

theorem radialTailStretch_deriv {A B c d : ℝ} (r : ℝ) :
    deriv (radialTailStretch A B c d) r =
      A + (B - A) * deriv (radialTailRamp c d) r := by
  exact ((hasDerivAt_const_mul A).add
    (((radialTailRamp_contDiff c d).differentiable (by simp) r).hasDerivAt.const_mul
      (B - A))).deriv

theorem radialTailStretch_deriv_lower {A B c d : ℝ}
    (hAB : A ≤ B) (hc : 0 < c) (hcd : c < d) (r : ℝ) :
    A ≤ deriv (radialTailStretch A B c d) r := by
  rw [radialTailStretch_deriv]
  have hg : 0 ≤ deriv (radialTailRamp c d) r :=
    (radialTailRamp_monotone hc hcd).deriv_nonneg
  have ht := mul_nonneg (sub_nonneg.mpr hAB) hg
  linarith

theorem radialTailStretch_gap {A B c d x y : ℝ}
    (hAB : A ≤ B) (hc : 0 < c) (hcd : c < d) (hxy : x ≤ y) :
    A * (y - x) ≤ radialTailStretch A B c d y - radialTailStretch A B c d x := by
  have hg := (radialTailRamp_monotone hc hcd) hxy
  have ht := mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hg)
  dsimp only [radialTailStretch]
  nlinarith

theorem radialTailStretch_strictMono {A B c d : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hc : 0 < c) (hcd : c < d) :
    StrictMono (radialTailStretch A B c d) := by
  intro x y hxy
  have hg := radialTailStretch_gap hAB hc hcd hxy.le
  have hp := mul_pos hA (sub_pos.mpr hxy)
  linarith

theorem radialTailStretch_surjective {A B c d : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hcd : c < d) :
    Function.Surjective (radialTailStretch A B c d) := by
  intro y
  have hB : 0 < B := hA.trans_le hAB
  let l : ℝ := min c (y / A)
  let h : ℝ := max d (y / B)
  have hlc : l ≤ c := min_le_left _ _
  have hdh : d ≤ h := le_max_left _ _
  have hlh : l ≤ h := hlc.trans (hcd.le.trans hdh)
  have hl : radialTailStretch A B c d l ≤ y := by
    rw [radialTailStretch_left hcd hlc]
    calc
      _ ≤ A * (y / A) := mul_le_mul_of_nonneg_left (min_le_right _ _) hA.le
      _ = y := by field_simp [hA.ne']
  have hh : y ≤ radialTailStretch A B c d h := by
    rw [radialTailStretch_right hcd hdh]
    calc
      y = B * (y / B) := by field_simp [hB.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hB.le
  obtain ⟨r, hr, hfr⟩ :=
    intermediate_value_Icc hlh (radialTailStretch_contDiff A B c d).continuous.continuousOn
      ⟨hl, hh⟩
  exact ⟨r, hfr⟩

theorem radialTailStretch_inverse_bound {A B c d : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hc : 0 < c) (hcd : c < d) (x y : ℝ) :
    |x - y| ≤ A⁻¹ * |radialTailStretch A B c d x - radialTailStretch A B c d y| := by
  have hmono := (radialTailStretch_strictMono hA hAB hc hcd).monotone
  have hgap : A * |x - y| ≤
      |radialTailStretch A B c d x - radialTailStretch A B c d y| := by
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr (hmono hxy))]
      have h := radialTailStretch_gap hAB hc hcd hxy
      nlinarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg (sub_nonneg.mpr (hmono hyx))]
      exact radialTailStretch_gap hAB hc hcd hyx
  have hh := (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hgap)
  simpa only [div_eq_mul_inv, mul_comm] using hh

theorem radialTailStretch_lipschitz {A B c d : ℝ} (hcd : c < d) :
    ∃ U : ℝ, 0 < U ∧ ∀ x y : ℝ,
      |radialTailStretch A B c d x - radialTailStretch A B c d y| ≤ U * |x - y| := by
  let f : ℝ → ℝ := radialTailStretch A B c d
  have hf : ContDiff ℝ ∞ f := radialTailStretch_contDiff A B c d
  obtain ⟨J, hJ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc c d) (hf.continuous_deriv (by simp)).continuousOn
  let U : ℝ := 1 + |A| + |B| + |J|
  have hU : 0 < U := by dsimp only [U]; positivity
  have hAU : |A| ≤ U := by dsimp only [U]; linarith [abs_nonneg B, abs_nonneg J]
  have hBU : |B| ≤ U := by dsimp only [U]; linarith [abs_nonneg A, abs_nonneg J]
  have hJU : J ≤ U := by
    dsimp only [U]
    linarith [le_abs_self J, abs_nonneg A, abs_nonneg B]
  have hderiv : ∀ r : ℝ, ‖deriv f r‖ ≤ U := by
    intro r
    by_cases hr : r ∈ Icc c d
    · exact (hJ r hr).trans hJU
    · by_cases hrc : r < c
      · have hg : f =ᶠ[𝓝 r] fun x => A * x := by
          filter_upwards [isOpen_Iio.mem_nhds hrc] with x hx
          exact radialTailStretch_left hcd hx.le
        rw [hg.deriv_eq, deriv_const_mul_id, Real.norm_eq_abs]
        exact hAU
      · have hdr : d < r := lt_of_not_ge (fun hrd => hr ⟨le_of_not_gt hrc, hrd⟩)
        have hg : f =ᶠ[𝓝 r] fun x => B * x := by
          filter_upwards [isOpen_Ioi.mem_nhds hdr] with x hx
          exact radialTailStretch_right hcd hx.le
        rw [hg.deriv_eq, deriv_const_mul_id, Real.norm_eq_abs]
        exact hBU
  refine ⟨U, hU, ?_⟩
  intro x y
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun r _ => hf.differentiable (by simp) r) (fun r _ => hderiv r)
    (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using h

/-- The new-to-old coordinate and its inverse, including exact tail
formulas, nonvanishing derivative, and a common metric constant. -/
theorem exists_smooth_tail_coordinate {A B c d : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hc : 0 < c) (hcd : c < d) :
    ∃ e : ℝ ≃o ℝ,
      ContDiff ℝ ∞ (fun r => e r) ∧
      ContDiff ℝ ∞ (fun r => e.symm r) ∧
      (∀ r, 0 < deriv (fun x => e x) r) ∧
      (∀ r ≤ c, e.symm r = A * r) ∧
      (∀ r, d ≤ r → e.symm r = B * r) ∧
      (∀ r ≤ A * c, e r = r / A) ∧
      (∀ r, B * d ≤ r → e r = r / B) ∧
      ∃ L : ℝ, 1 ≤ L ∧
        (∀ x y : ℝ, |e x - e y| ≤ L * |x - y|) ∧
        (∀ x y : ℝ, |x - y| ≤ L * |e x - e y|) := by
  let f : ℝ → ℝ := radialTailStretch A B c d
  have hf : ContDiff ℝ ∞ f := radialTailStretch_contDiff A B c d
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hmono : StrictMono f := radialTailStretch_strictMono hA hAB hc hcd
  have hsurj : Function.Surjective f := radialTailStretch_surjective hA hAB hcd
  have hderivpos (r : ℝ) : 0 < deriv f r :=
    hA.trans_le (radialTailStretch_deriv_lower hAB hc hcd r)
  let E : ℝ ≃o ℝ :=
    { toFun := f
      invFun := Function.surjInv hsurj
      left_inv := fun r => hmono.injective (Function.rightInverse_surjInv hsurj (f r))
      right_inv := Function.rightInverse_surjInv hsurj
      map_rel_iff' := hmono.le_iff_le }
  have hEf (r : ℝ) : E r = f r := rfl
  have hEfun : (fun r => E r) = f := funext hEf
  have hEsmooth : ContDiff ℝ ∞ (fun r => E r) := by rw [hEfun]; exact hf
  have hInvsmooth : ContDiff ℝ ∞ (fun r => E.symm r) := by
    apply E.toHomeomorph.contDiff_symm
      (f₀' := fun r => ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0 (deriv f r) (hderivpos r).ne'))
    · intro r
      change HasFDerivAt (fun x => E x) _ r
      rw [hEfun]
      exact (hfd r).hasDerivAt.hasFDerivAt_equiv (hderivpos r).ne'
    · exact hEsmooth
  have hEfInv (r : ℝ) : f (E.symm r) = r := by
    rw [← hEf]
    exact E.apply_symm_apply r
  have hInvderiv (r : ℝ) : 0 < deriv (fun x => E.symm x) r := by
    have hDE : HasDerivAt (fun x => E x) (deriv f (E.symm r)) (E.symm r) := by
      rw [hEfun]
      exact (hfd _).hasDerivAt
    have hInv := HasDerivAt.of_local_left_inverse E.symm.continuous.continuousAt
      hDE (hderivpos _).ne' (Eventually.of_forall E.apply_symm_apply)
    rw [hInv.deriv]
    exact inv_pos.mpr (hderivpos _)
  have hleft (r : ℝ) (hr : r ≤ c) : E r = A * r := by
    rw [hEf]
    exact radialTailStretch_left hcd hr
  have hright (r : ℝ) (hr : d ≤ r) : E r = B * r := by
    rw [hEf]
    exact radialTailStretch_right hcd hr
  have hleftInv (r : ℝ) (hr : r ≤ A * c) : E.symm r = r / A := by
    have hrc : E.symm r ≤ c := by
      apply E.le_iff_le.mp
      simpa only [E.apply_symm_apply, hleft c le_rfl] using hr
    apply (eq_div_iff hA.ne').mpr
    calc
      _ = A * E.symm r := mul_comm _ _
      _ = E (E.symm r) := (hleft _ hrc).symm
      _ = r := E.apply_symm_apply r
  have hB : 0 < B := hA.trans_le hAB
  have hrightInv (r : ℝ) (hr : B * d ≤ r) : E.symm r = r / B := by
    have hdr : d ≤ E.symm r := by
      apply E.le_iff_le.mp
      simpa only [E.apply_symm_apply, hright d le_rfl] using hr
    apply (eq_div_iff hB.ne').mpr
    calc
      _ = B * E.symm r := mul_comm _ _
      _ = E (E.symm r) := (hright _ hdr).symm
      _ = r := E.apply_symm_apply r
  obtain ⟨U, hU, hLip⟩ := radialTailStretch_lipschitz (A := A) (B := B) hcd
  let L : ℝ := max 1 (max U A⁻¹)
  have hUL : U ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hAL : A⁻¹ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨E.symm, hInvsmooth, hEsmooth, hInvderiv, hleft, hright,
    hleftInv, hrightInv, L, le_max_left _ _, ?_, ?_⟩
  · intro x y
    have h := radialTailStretch_inverse_bound hA hAB hc hcd (E.symm x) (E.symm y)
    change |E.symm x - E.symm y| ≤ A⁻¹ * |f (E.symm x) - f (E.symm y)| at h
    rw [hEfInv, hEfInv] at h
    exact h.trans (mul_le_mul_of_nonneg_right hAL (abs_nonneg _))
  · intro x y
    have h := hLip (E.symm x) (E.symm y)
    change |f (E.symm x) - f (E.symm y)| ≤ U * |E.symm x - E.symm y| at h
    rw [hEfInv, hEfInv] at h
    exact h.trans (mul_le_mul_of_nonneg_right hUL (abs_nonneg _))

end ContinuousFlexibility.Radial
