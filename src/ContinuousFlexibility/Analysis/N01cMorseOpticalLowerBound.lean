import ContinuousFlexibility.Radial.MorseRealizationBasic
import ContinuousFlexibility.Radial.MorseRetainedRadiusModelBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Quantitative optical nondegeneracy of the actual Morse realization

This module derives a lower bound for
`-w'(r) / (r * w(r))` from the actual radius equation and profile pullback
in `MorseChainRealization`.  It does not assume an optical-speed estimate.
The profile amplitude cancels in the exact identity.  The numerical lower
bound is uniform on each whole negative model component, including its
approach to either turning point.

The theorem applies to tail indices `100 ≤ n`.  It does not identify the
Morse realization with an arbitrary `IsRadialReference`, or choose the cell
indices of a nonlinear geometry witness.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped ContDiff Topology

private theorem n01c_exp_linear_lower (u v : ℝ) :
    exp u * (v - u) ≤ exp v - exp u := by
  have h := mul_le_mul_of_nonneg_left (add_one_le_exp (v - u)) (exp_pos u).le
  calc
    exp u * (v - u) = exp u * ((v - u) + 1) - exp u := by ring
    _ ≤ exp u * exp (v - u) - exp u := sub_le_sub_right h _
    _ = exp v - exp u := by
      rw [← exp_add, show u + (v - u) = v by ring]

/-- The retained left cut lies strictly before the first true turning point. -/
theorem n01c_morseCellLeftCut_lt_leftTurn {A B : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) :
    morseCellLeftCut < morseLeftTurn A B := by
  have hroot := (morseRootT_bounds hB hAB).2.2.2
  have he : exp (-morseLeftTurn A B) < exp (-morseCellLeftCut) := by
    rw [exp_neg_morseLeftTurn hB hAB, exp_neg_morseCellLeftCut]
    exact hroot.trans (by norm_num)
  have hh := exp_lt_exp.mp he
  linarith only [hh]

/-- A distance lower bound on the entire positive lobe of the actual Morse
coefficient.  The separation hypothesis is a numerical parameter inequality;
the realized tail parameters satisfy it below. -/
theorem n01c_morseRho_lower_distance {A B X : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hseparation : 16 * B ≤ 3 * A)
    (hX : X ∈ Ioo (morseLeftTurn A B) (morseRightTurn A B)) :
    (B / 4) * min (X - morseLeftTurn A B) (morseRightTurn A B - X) ≤
      morseRho A B X := by
  let r := morseRightRootT A B
  let l := morseLeftRootT A B
  let t := exp (-X)
  let δ := min (X - morseLeftTurn A B) (morseRightTurn A B - X)
  let u := t - r
  let v := l - t
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hr : 0 < r := (morseRootT_bounds hB hAB).1
  have hδ : 0 ≤ δ := le_min (sub_nonneg.mpr hX.1.le) (sub_nonneg.mpr hX.2.le)
  have hrt : r ≤ t := by
    change morseRightRootT A B ≤ exp (-X)
    rw [← exp_neg_morseRightTurn hB hAB]
    exact exp_le_exp.mpr (neg_le_neg hX.2.le)
  have htl : t ≤ l := by
    change exp (-X) ≤ morseLeftRootT A B
    rw [← exp_neg_morseLeftTurn hB hAB]
    exact exp_le_exp.mpr (neg_le_neg hX.1.le)
  have hu : 0 ≤ u := sub_nonneg.mpr hrt
  have hv : 0 ≤ v := sub_nonneg.mpr htl
  have hright : r * δ ≤ u := by
    calc
      r * δ ≤ r * (morseRightTurn A B - X) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hr.le
      _ ≤ u := by
        have hh := n01c_exp_linear_lower (-morseRightTurn A B) (-X)
        rw [show (-X) - (-morseRightTurn A B) = morseRightTurn A B - X by ring,
          exp_neg_morseRightTurn hB hAB] at hh
        exact hh
  have hleft : r * δ ≤ v := by
    calc
      r * δ ≤ t * (X - morseLeftTurn A B) :=
        mul_le_mul hrt (min_le_left _ _) hδ (exp_pos (-X)).le
      _ ≤ v := by
        have hh := n01c_exp_linear_lower (-X) (-morseLeftTurn A B)
        rw [show (-morseLeftTurn A B) - (-X) = X - morseLeftTurn A B by ring,
          exp_neg_morseLeftTurn hB hAB] at hh
        exact hh
  have hdisc : (1 / 4 : ℝ) ≤ 1 - 4 * B / A := by
    have hh : 4 * B / A ≤ (3 / 4 : ℝ) :=
      (div_le_iff₀ hA).mpr (by linarith only [hseparation])
    linarith only [hh]
  have hsquare := sq_sqrt ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans hdisc)
  have hsqrt := sqrt_nonneg (1 - 4 * B / A)
  have hsqrtLower : (1 / 2 : ℝ) ≤ sqrt (1 - 4 * B / A) := by
    nlinarith only [hsquare, hsqrt, hdisc]
  have hgap : (1 / 2 : ℝ) ≤ l - r := by
    dsimp only [l, r, morseLeftRootT, morseRightRootT]
    linarith only [hsqrtLower]
  have hsum : u + v = l - r := by dsimp only [u, v]; ring
  have hprod : (r * δ) * (1 / 4 : ℝ) ≤ u * v := by
    rcases le_total u v with huv | hvu
    · have hvquarter : (1 / 4 : ℝ) ≤ v := by linarith only [hgap, hsum, huv]
      exact mul_le_mul hright hvquarter (by norm_num) hu
    · have huquarter : (1 / 4 : ℝ) ≤ u := by linarith only [hgap, hsum, hvu]
      have hh := mul_le_mul huquarter hleft (mul_nonneg hr.le hδ) hu
      simpa only [mul_comm] using hh
  have hBr : B ≤ A * r := by
    have hh := (div_le_iff₀ hA).mp (morseRightRootT_ratio_bounds hB hAB).1
    exact hh.trans_eq (mul_comm _ _)
  calc
    (B / 4) * δ = B * (δ / 4) := by ring
    _ ≤ (A * r) * (δ / 4) :=
      mul_le_mul_of_nonneg_right hBr (div_nonneg hδ (by norm_num))
    _ = A * ((r * δ) * (1 / 4 : ℝ)) := by ring
    _ ≤ A * (u * v) := mul_le_mul_of_nonneg_left hprod hA.le
    _ = morseRho A B X := by
      dsimp only [u, v, t, r, l]
      rw [morseRho_factor hB hAB]
      ring

private theorem n01c_min_image_distance_le {R : ℝ → ℝ} {l r X M : ℝ}
    (hR : ContDiff ℝ ∞ R) (hX : X ∈ Ioo l r)
    (hM : ∀ t ∈ Icc l r, deriv R t ≤ M) :
    min (R X - R l) (R r - R X) ≤ M * min (X - l) (r - X) := by
  have hlr : l ≤ r := (hX.1.trans hX.2).le
  have hL := (convex_Icc l r).image_sub_le_mul_sub_of_deriv_le
    hR.continuous.continuousOn (hR.differentiable (by simp)).differentiableOn
    (fun t ht => hM t (interior_subset ht))
    l (left_mem_Icc.mpr hlr) X (Ioo_subset_Icc_self hX) hX.1.le
  have hR' := (convex_Icc l r).image_sub_le_mul_sub_of_deriv_le
    hR.continuous.continuousOn (hR.differentiable (by simp)).differentiableOn
    (fun t ht => hM t (interior_subset ht))
    X (Ioo_subset_Icc_self hX) r (right_mem_Icc.mpr hlr) hX.2.le
  rcases le_total (X - l) (r - X) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hL
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans hR'

/-- Dilation of the physical radius changes the optical ratio by the inverse
square of the dilation.  The constant height scale cancels.  The hypothesis
is an equality of actual profile germs, not an independently prescribed jet. -/
theorem n01c_opticalRatio_dilation {W w : ℝ → ℝ} {scale heightScale r : ℝ}
    (hW : DifferentiableAt ℝ W (scale * r)) (hw : DifferentiableAt ℝ w r)
    (hscale : scale ≠ 0) (hheightScale : heightScale ≠ 0) (hr : r ≠ 0) (hwr : w r ≠ 0)
    (he : (fun t => W (scale * t)) =ᶠ[𝓝 r] (fun t => (heightScale * scale) * w t)) :
    -(deriv W (scale * r)) / ((scale * r) * W (scale * r)) =
      (-(deriv w r) / (r * w r)) / scale ^ 2 := by
  have hscaleDeriv : HasDerivAt (fun t : ℝ => scale * t) scale r := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id r).const_mul scale
  have hDL : HasDerivAt (fun t => W (scale * t)) (deriv W (scale * r) * scale) r :=
    hW.hasDerivAt.comp r hscaleDeriv
  have hDR : HasDerivAt (fun t => (heightScale * scale) * w t) ((heightScale * scale) * deriv w r) r :=
    hw.hasDerivAt.const_mul (heightScale * scale)
  have hD : deriv W (scale * r) * scale = (heightScale * scale) * deriv w r :=
    hDL.deriv.symm.trans (he.deriv_eq.trans hDR.deriv)
  have hWd : deriv W (scale * r) = heightScale * deriv w r := by
    apply mul_right_cancel₀ hscale
    calc
      deriv W (scale * r) * scale = (heightScale * scale) * deriv w r := hD
      _ = (heightScale * deriv w r) * scale := by ring
  rw [hWd, he.eq_of_nhds]
  field_simp [hscale, hheightScale, hr, hwr] <;> ring

end ContinuousFlexibility.Radial

namespace ContinuousFlexibility.Statements

open Real Set Filter
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

namespace MorseChainRealization

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}

/-- The optical ratio is exactly the actual Morse coefficient divided by the
square of the actual radius speed.  This follows by differentiating the
profile equality in the realization; the height amplitude cancels. -/
theorem opticalRatio_at_radius (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) {X : ℝ}
    (hX : X ∈ Ioo (T.leftX side n) (T.rightX side n)) :
    -(deriv D.w (T.radius side n X)) /
        (T.radius side n X * D.w (T.radius side n X)) =
      morseRho (morseChainA T n) (morseChainB T n) X /
        (deriv (T.radius side n) X) ^ 2 := by
  let R := T.radius side n
  let amp := morseChainAmplitude T σ n
  let ρ := morseRho (morseChainA T n) (morseChainB T n) X
  have hRc : ContDiff ℝ ∞ R := h.radius_smooth side n hn
  have hWc : ContDiff ℝ ∞ D.w := h.geometry.2.2.1.1
  have hV : 0 < deriv R X := h.derivative_positive side n hn X (Ioo_subset_Icc_self hX)
  have hR : 0 < R X := h.radius_positive side n hn X (Ioo_subset_Icc_self hX)
  have hW : 0 < D.w (R X) :=
    h.geometry.2.2.2.2.1 _ (h.radius_mem_core side n hn X (Ioo_subset_Icc_self hX))
  have hprofile : D.w (R X) = amp * deriv R X :=
    h.profile_eq side n hn X (Ioo_subset_Icc_self hX)
  have hamp : amp ≠ 0 := by
    intro he
    rw [hprofile, he, zero_mul] at hW
    exact (lt_irrefl (0 : ℝ)) hW
  have hEq : deriv (deriv R) X = -ρ * R X :=
    h.equation side n hn X (Ioo_subset_Icc_self hX)
  have he : (fun t => D.w (R t)) =ᶠ[𝓝 X] (fun t => amp * deriv R t) := by
    filter_upwards [Ioo_mem_nhds hX.1 hX.2] with t ht
    exact h.profile_eq side n hn t (Ioo_subset_Icc_self ht)
  have hDL : HasDerivAt (fun t => D.w (R t))
      (deriv D.w (R X) * deriv R X) X :=
    ((hWc.differentiable (by simp) (R X)).hasDerivAt).comp X
      ((hRc.differentiable (by simp) X).hasDerivAt)
  have hDR : HasDerivAt (fun t => amp * deriv R t)
      (amp * deriv (deriv R) X) X :=
    ((((contDiff_infty_iff_deriv.mp hRc).2.differentiable (by simp) X).hasDerivAt).const_mul amp)
  have hprod : deriv D.w (R X) * deriv R X = -amp * ρ * R X := by
    have hh := hDL.deriv.symm.trans (he.deriv_eq.trans hDR.deriv)
    rw [hEq] at hh
    nlinarith only [hh]
  have hderiv : deriv D.w (R X) = -amp * ρ * R X / deriv R X :=
    (eq_div_iff hV.ne').mpr hprod
  change -(deriv D.w (R X)) / (R X * D.w (R X)) = ρ / (deriv R X) ^ 2
  rw [hderiv, hprofile]
  field_simp [hamp, hR.ne', hV.ne'] <;> ring

private theorem n01c_parameter_bounds (h : MorseChainRealization T σ D C)
    (n : ℕ) (hn : T.index ≤ n) (h100 : 100 ≤ n) :
    morseChainA T n ≤ 1 / 1000 ∧
      morseChainA T n ^ 9 / (9 : ℝ) ^ 9 ≤ morseChainB T n ∧
      morseChainB T n ≤ morseChainA T n ^ 9 ∧
      16 * morseChainB T n ≤ 3 * morseChainA T n := by
  have hd1 : 1 ≤ (T.d n : ℝ) :=
    (one_le_exp_iff.mpr (sq_nonneg (n : ℝ))).trans (h.1 n hn).1
  have hBA := morseChainB_A_bounds T n hd1
  have hA₀ : morseChainA T n ≤ 1 / 1000 := by
    apply morseChainA_le_of_sq_ge_log T n (h.d_eq n hn) (by norm_num)
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast h100
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hnR 2
    have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9 / (1 / 1000 : ℝ))
    norm_num at hsq hlog ⊢
    linarith only [hlog, hsq]
  have hA : 0 ≤ morseChainA T n := sq_nonneg _
  have hhalf : morseChainA T n ≤ 1 / 2 := hA₀.trans (by norm_num)
  have h8 := pow_le_pow_left₀ hA hhalf 8
  have hBsmall : morseChainB T n ≤ morseChainA T n / 256 := by
    calc
      morseChainB T n ≤ morseChainA T n ^ 9 := hBA.2
      _ = morseChainA T n * morseChainA T n ^ 8 := by ring
      _ ≤ morseChainA T n * (1 / 2 : ℝ) ^ 8 := mul_le_mul_of_nonneg_left h8 hA
      _ = morseChainA T n / 256 := by norm_num; ring
  exact ⟨hA₀, hBA.1, hBA.2, by linarith only [hBsmall, hA]⟩

/-- Normalizing the same radius by its value at the right root gives the
actual velocity upper bound throughout the left retained interval. -/
theorem radius_deriv_le_seven_b_mul_A (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (h100 : 100 ≤ n)
    (X : ℝ) (hX : X ∈ Icc (T.leftX side n) (morseChainRightTurn T n)) :
    deriv (T.radius side n) X ≤ 7 * D.b * morseChainA T n := by
  let A := morseChainA T n
  let B := morseChainB T n
  let R := T.radius side n
  let s := R (morseChainRightTurn T n)
  let r : ℝ → ℝ := fun x => R x / s
  obtain ⟨hB, hAB, hleft, hab, hbe, _, hspeed⟩ := h.retained_data side n hn
  obtain ⟨hA₀, hBAlo, hBAhi, _⟩ := n01c_parameter_bounds h n hn h100
  have hs : 0 < s := h.radius_positive side n hn _ ⟨hab.le, hbe.le⟩
  have hsb : s ≤ D.b := (h.radius_mem_core side n hn _ ⟨hab.le, hbe.le⟩).2.le
  have hR : ContDiff ℝ ∞ R := h.radius_smooth side n hn
  have hr : ContDiff ℝ ∞ r := hR.div_const s
  have hd (x : ℝ) : deriv r x = deriv R x / s :=
    (((hR.differentiable (by simp) x).hasDerivAt).div_const s).deriv
  have hdd (x : ℝ) : deriv (deriv r) x = deriv (deriv R) x / s := by
    have he : deriv r = fun y => deriv R y / s := funext hd
    rw [he]
    exact ((((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) x).hasDerivAt).div_const s).deriv
  have hrroot : r (morseRightTurn A B) = 1 := by
    change s / s = 1
    exact div_self hs.ne'
  have hvroot : deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 := by
    rw [hd]
    change deriv (T.radius side n) (morseChainRightTurn T n) / s = _
    rw [hspeed]
    change ((1 / 100 : ℝ) * A ^ 5 * s) / s = _
    exact mul_div_cancel_right₀ _ hs.ne'
  have hturn : morseChainRightTurn T n = morseRightTurn A B := rfl
  have hsub (y : ℝ) (hy : y ∈ Icc morseCellLeftCut (morseRightTurn A B)) :
      y ∈ Icc (T.leftX side n) (T.rightX side n) := by
    have hy' : y ∈ Icc (T.leftX side n) (morseChainRightTurn T n) := by
      simpa only [hleft, hturn, morseCellLeftCut] using hy
    exact ⟨hy'.1, hy'.2.trans hbe.le⟩
  have hEq (y : ℝ) (hy : y ∈ Icc morseCellLeftCut (morseRightTurn A B)) :
      deriv (deriv r) y = -morseRho A B y * r y := by
    rw [hdd, h.equation side n hn y (hsub y hy)]
    dsimp only [r, R, A, B]
    ring
  have hLeft := (morseLeftCap_radius_bounds hB hAB hA₀ hBAlo hBAhi hr hrroot hvroot hEq).1
  have hX' : X ∈ Icc morseCellLeftCut (morseRightTurn A B) := by
    simpa only [hleft, hturn, morseCellLeftCut] using hX
  have hv : deriv R X / s ≤ 7 * A := by
    rw [← hd]
    exact (hLeft X hX').2.2.2.2
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  calc
    deriv R X ≤ (7 * A) * s := (div_le_iff₀ hs).mp hv
    _ ≤ (7 * A) * D.b := mul_le_mul_of_nonneg_left hsb (by positivity)
    _ = 7 * D.b * A := by ring

/-- A quantitative lower bound for the actual optical ratio throughout the
whole negative Morse component.  There are no assumed optical or flow bounds.
The denominator uses only the fixed outer radius and the actual cell scale. -/
theorem opticalRatio_lower_bound (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (h100 : 100 ≤ n)
    (X : ℝ)
    (hX : X ∈ Ioo (morseLeftTurn (morseChainA T n) (morseChainB T n))
      (morseChainRightTurn T n)) :
    (morseChainB T n / (1372 * D.b ^ 3 * morseChainA T n ^ 3)) *
        min (T.radius side n X -
          T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
          (T.radius side n (morseChainRightTurn T n) - T.radius side n X) ≤
      -(deriv D.w (T.radius side n X)) /
        (T.radius side n X * D.w (T.radius side n X)) := by
  let A := morseChainA T n
  let B := morseChainB T n
  let R := T.radius side n
  let l := morseLeftTurn A B
  let r := morseChainRightTurn T n
  let ρ := morseRho A B X
  let δ := min (R X - R l) (R r - R X)
  let δX := min (X - l) (r - X)
  let M := 7 * D.b * A
  let Q := -(deriv D.w (R X)) / (R X * D.w (R X))
  change X ∈ Ioo l r at hX
  obtain ⟨hB, hAB, hleft, _, hbe, _, _⟩ := h.retained_data side n hn
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hb : 0 < D.b := h.geometry.1.trans h.geometry.2.1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hcut : T.leftX side n < l := by
    rw [hleft]
    exact n01c_morseCellLeftCut_lt_leftTurn hB hAB
  have hXi : X ∈ Ioo (T.leftX side n) (T.rightX side n) :=
    ⟨hcut.trans hX.1, hX.2.trans hbe⟩
  have hv : 0 < deriv R X := h.derivative_positive side n hn X (Ioo_subset_Icc_self hXi)
  have hV (y : ℝ) (hy : y ∈ Icc l r) : deriv R y ≤ M :=
    h.radius_deriv_le_seven_b_mul_A side n hn h100 y ⟨hcut.le.trans hy.1, hy.2⟩
  have hδ : δ ≤ M * δX :=
    n01c_min_image_distance_le (h.radius_smooth side n hn) hX hV
  have hsep := (n01c_parameter_bounds h n hn h100).2.2.2
  have hρ : (B / 4) * δX ≤ ρ := n01c_morseRho_lower_distance hB hAB hsep hX
  have hρpos : 0 < ρ := morseRho_pos_between_turns hB hAB hX
  have hQeq : Q = ρ / (deriv R X) ^ 2 := h.opticalRatio_at_radius side n hn hXi
  have hQpos : 0 < Q := by rw [hQeq]; exact div_pos hρpos (pow_pos hv 2)
  have hQmul : ρ = Q * (deriv R X) ^ 2 :=
    (div_eq_iff (pow_ne_zero 2 hv.ne')).mp hQeq.symm
  have hsquare : (deriv R X) ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ hv.le (hV X (Ioo_subset_Icc_self hX)) 2
  have hBδ : B * δ ≤ 4 * M * ρ := by
    calc
      B * δ ≤ B * (M * δX) := mul_le_mul_of_nonneg_left hδ hB.le
      _ = M * (B * δX) := by ring
      _ ≤ M * (4 * ρ) :=
        mul_le_mul_of_nonneg_left (by linarith only [hρ]) hM.le
      _ = 4 * M * ρ := by ring
  have hcross : B * δ ≤ (1372 * D.b ^ 3 * A ^ 3) * Q := by
    calc
      B * δ ≤ 4 * M * ρ := hBδ
      _ = (4 * M * Q) * (deriv R X) ^ 2 := by rw [hQmul]; ring
      _ ≤ (4 * M * Q) * M ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = (1372 * D.b ^ 3 * A ^ 3) * Q := by dsimp only [M]; ring
  have hden : 0 < 1372 * D.b ^ 3 * A ^ 3 := by positivity
  change (B / (1372 * D.b ^ 3 * A ^ 3)) * δ ≤ Q
  calc
    (B / (1372 * D.b ^ 3 * A ^ 3)) * δ =
        (B * δ) / (1372 * D.b ^ 3 * A ^ 3) := by ring
    _ ≤ Q := (div_le_iff₀ hden).mpr (hcross.trans_eq (mul_comm _ _))

/-- The same lower bound stated at every physical radius of the negative
model component.  The actual continuous radius supplies the coordinate by
the intermediate value theorem. -/
theorem opticalRatio_lower_bound_on_component (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (h100 : 100 ≤ n)
    (r : ℝ)
    (hr : r ∈ Ioo
      (T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
      (T.radius side n (morseChainRightTurn T n))) :
    (morseChainB T n / (1372 * D.b ^ 3 * morseChainA T n ^ 3)) *
        min (r - T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)))
          (T.radius side n (morseChainRightTurn T n) - r) ≤
      -(deriv D.w r) / (r * D.w r) := by
  have hdata := h.retained_data side n hn
  have horder : morseLeftTurn (morseChainA T n) (morseChainB T n) <
      morseChainRightTurn T n := morseTurn_order hdata.1 hdata.2.1
  obtain ⟨X, hX, rfl⟩ := intermediate_value_Ioo horder.le
    (h.radius_smooth side n hn).continuous.continuousOn hr
  exact h.opticalRatio_lower_bound side n hn h100 X hX

end MorseChainRealization

end ContinuousFlexibility.Statements
