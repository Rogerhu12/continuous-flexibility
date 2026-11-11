import ContinuousFlexibility.Radial.MatchedTerminalLeadingBounds
import ContinuousFlexibility.Radial.TerminalMorseLiftEnergy

/-!
# Leading-column bounds on the original terminal Morse caps

The same physical radius, cutoff and normalized stand-in are used
throughout. The two endpoint choices share one scalar convexity argument.
The physical norm estimate cancels the dilation and profile height,
leaving only 400 / (j A²).
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The actual normalized stand-in stays within the unit interval in
absolute value on its entire original cap. -/
theorem terminalMorseCap_value_bound (long : Bool)
    {A B j s weightScale : ℝ} {r w u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hscale : weightScale ≠ 0)
    (hA₀ : A ≤ 1 / 1000) (hBA : B ≤ A ^ 9)
    (hr : IsNormalizedMorseCell A B r)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hode : ∀ x ∈ Icc (if long then morseRightTurn A B else morseCellLeftCut)
        (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut),
      radialJacobi (j ^ 2) w u (s * r x) = 0)
    (hzero : u (s * r (if long then morseRightTurn A B else morseShortLeftCapCut)) = 0)
    (hjoin : u (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) = 1) :
    ∀ z ∈ Icc (terminalMorseLayerRadius long A B s r 0)
      (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)),
      |u z| ≤ 1 := by
  let R := terminalMorseLayerRadius long A B s r
  let L := terminalMorseLayerLength long A
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hR : ContDiff ℝ ∞ R := terminalMorseLayerRadius_smooth long A B s hr.smooth
  have hweightR (x : ℝ) (hx : x ∈ Icc 0 L) :
      w (R x) = weightScale * deriv R x := by
    change w (s * r (terminalMorseLayerOrigin long A B + 1 * x)) =
      weightScale * deriv (terminalMorseCapRadius s
        (terminalMorseLayerOrigin long A B) 1 r) x
    rw [terminalMorseCapRadius_deriv _ _ _ _ hr.smooth]
    simpa only [one_mul, mul_one] using
      hweight _ (terminalMorseLayer_point_mem long hB hAB hx)
  have hodeR (x : ℝ) (hx : x ∈ Icc 0 L) :
      radialJacobi (j ^ 2) w u (R x) = 0 := by
    simpa only [R, terminalMorseLayerRadius, terminalMorseCapRadius, one_mul] using
      hode _ (terminalMorseLayer_cap_point_mem long hx)
  have hpotential (x : ℝ) (hx : x ∈ Ioo 0 L) :
      0 ≤ j ^ 2 * deriv (deriv R) x / R x := by
    have hx' := Ioo_subset_Icc_self hx
    have hpos := terminalMorseLayerRadius_pos long hB hAB hs hr hx'
    have hq := (terminalMorseLayer_rho_bounds long hB hAB hA₀ hBA hx').1
    rw [show deriv (deriv R) x =
        -morseRho A B (terminalMorseLayerOrigin long A B + x) * R x from
      terminalMorseLayerRadius_equation long hB hAB hs hr hx']
    have he : j ^ 2 *
        (-morseRho A B (terminalMorseLayerOrigin long A B + x) * R x) / R x =
        j ^ 2 * (-morseRho A B (terminalMorseLayerOrigin long A B + x)) := by
      simpa only [mul_assoc] using
        mul_div_cancel_right₀
          (j ^ 2 * (-morseRho A B (terminalMorseLayerOrigin long A B + x)))
          (show R x ≠ 0 from hpos.ne')
    rw [he]
    exact mul_nonneg (sq_nonneg _) hq
  have hends := terminalMorseCap_endpoints long A B s r
  have ha : |u (R 0)| ≤ 1 := by
    rw [show R 0 = s * r (if long then morseRightTurn A B else morseCellLeftCut)
      from hends.1]
    cases long
    · simp only [Bool.false_eq_true, ite_false] at hjoin ⊢
      rw [hjoin]
      norm_num
    · simp only [eq_self_iff_true, ite_true] at hzero ⊢
      rw [hzero]
      norm_num
  have hb : |u (R L)| ≤ 1 := by
    rw [show R L = s * r (if long then morseRightCapEnd A B (1 / 100)
      else morseShortLeftCapCut) from hends.2]
    cases long
    · simp only [Bool.false_eq_true, ite_false] at hzero ⊢
      rw [hzero]
      norm_num
    · simp only [eq_self_iff_true, ite_true] at hjoin ⊢
      rw [hjoin]
      norm_num
  have hvalue := terminalCap_physical_amplitude_bound hL hscale (by norm_num : (0 : ℝ) ≤ 1)
    hR hw hu hweightR hodeR hpotential ha hb
  intro z hz
  obtain ⟨t, ht, htz⟩ := terminalMorseCap_preimage long hB hAB hs hr hz
  rw [← htz]
  exact hvalue t ht

/-- The original physical cutoff leading vector has a uniform
polynomial bound. The actual weight is charged only on this cap. -/
theorem terminalMorseCapInnerLift_weighted_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (long : Bool)
    {A B j s weightScale lam l h W : ℝ} {r u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hs : 0 < s)
    (hscale : 0 < weightScale) (hA₀ : A ≤ 1 / 1000) (hBA : B ≤ A ^ 9)
    (hr : IsNormalizedMorseCell A B r)
    (hw : ContDiff ℝ ∞ D.w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      D.w (s * r x) = weightScale * (s * deriv r x))
    (hode : ∀ x ∈ Icc (if long then morseRightTurn A B else morseCellLeftCut)
        (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut),
      radialJacobi (j ^ 2) D.w u (s * r x) = 0)
    (hzero : u (s * r (if long then morseRightTurn A B else morseShortLeftCapCut)) = 0)
    (hjoin : u (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) = 1)
    (hnorm : lam = standInBoundaryScale (j ^ 2)
      (D.w (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
    (hcap : Icc (terminalMorseLayerRadius long A B s r 0)
      (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) ⊆ Icc l h)
    (hterminal : if long then
      h = terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)
      else l = terminalMorseLayerRadius long A B s r 0)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (weight : ℝ → ℝ)
    (hE : ∀ f, E f =ᵐ[radialHilbertMeasure D] fun z => weight z * f z)
    (hW : 0 ≤ W)
    (hlocal : ∀ᵐ z ∂radialHilbertMeasure D,
      z ∈ Icc (terminalMorseLayerRadius long A B s r 0)
        (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) →
      |weight z| ≤ W) :
    ‖(E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
      (terminalCapInnerLift hD l h lam
        (terminalMorsePhysicalCutoff_smooth long A B s r) hu)‖ ≤
      W * (400 / (j * A ^ 2)) := by
  let R := terminalMorseLayerRadius long A B s r
  let L := terminalMorseLayerLength long A
  let a := R 0
  let b := R L
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hab : a < b := terminalMorseCap_radius_order long hB hAB hs hr
  have ha : s / 2 ≤ a := by
    have hlo := terminalMorse_retained_radius_lower hA₀ hr
      (terminalMorseLayer_point_mem long hB hAB
        (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩))
    calc
      s / 2 = s * (1 / 2) := by ring
      _ ≤ s * r (terminalMorseLayerOrigin long A B + 0) :=
        mul_le_mul_of_nonneg_left hlo hs.le
      _ = a := by simp only [a, R, terminalMorseLayerRadius, terminalMorseCapRadius, mul_zero]
  have ha₀ : 0 < a := (by positivity : 0 < s / 2).trans_le ha
  have hcoeff (z : ℝ) (hz : z ∈ Icc a b) :
      0 < z ∧ z ≤ 2 * s ∧ 0 < D.w z ∧ D.w z ≤ 7 * weightScale * s * A :=
    terminalMorseCap_physical_coefficients long hB hAB hs hscale hA₀ hr hweight hz
  have hdhi : b - a ≤ 2 * s := by
    have hb := (hcoeff b ⟨hab.le, le_rfl⟩).2.1
    linarith
  have hρ : ∀ z ∈ Icc a b,
      12 * D.w z / z ^ 2 ≤ 12 * (7 * weightScale * s * A) / a ^ 2 := by
    apply terminalCapLayer_density_le D ha₀ (by positivity)
    intro z hz
    rw [abs_of_pos (hcoeff z hz).2.2.1]
    exact (hcoeff z hz).2.2.2
  have hlam := terminalMorse_boundary_normalization_lower long hB hAB hs hscale hr hweight hnorm
  have hlam₀ : 0 < lam :=
    (by positivity : 0 < j ^ 2 * weightScale * A ^ 5 / 200).trans_le hlam
  have hmono : StrictMonoOn R (Icc 0 L) :=
    terminalMorseLayerRadius_strictMono long hB hAB hs hr
  have haLayer : a ≤ terminalMorseLayerLeft long A B s r :=
    hmono.monotoneOn ⟨le_rfl, hL.le⟩
      (show L / 4 ∈ Icc 0 L by constructor <;> linarith)
      (by linarith)
  have hbLayer : terminalMorseLayerRight long A B s r ≤ b :=
    hmono.monotoneOn (show L / 2 ∈ Icc 0 L by constructor <;> linarith)
      ⟨hL.le, le_rfl⟩ (by linarith)
  have hcover : ∀ z ∈ Icc l h,
      terminalMorsePhysicalCutoff long A B s r z ≠ 0 → z ∈ Icc a b := by
    intro z hz hχ
    have hzside := terminalPhysicalCutoff_support long
      (terminalMorseLayer_order long hB hAB hs hr) hχ
    cases long
    · change l = a at hterminal
      change z < terminalMorseLayerRight false A B s r at hzside
      exact ⟨hterminal ▸ hz.1, hzside.le.trans hbLayer⟩
    · change h = b at hterminal
      change terminalMorseLayerLeft true A B s r < z at hzside
      exact ⟨haLayer.trans hzside.le, hterminal ▸ hz.2⟩
  have hcutoff : ∀ z ∈ Icc a b, |terminalMorsePhysicalCutoff long A B s r z| ≤ 1 := by
    intro z _
    have hz := terminalPhysicalCutoff_range long
      (terminalMorseLayerLeft long A B s r) (terminalMorseLayerRight long A B s r) z
    exact (abs_of_nonneg hz.1).trans_le hz.2
  have hvalue := terminalMorseCap_value_bound long hB hAB hs hscale.ne'
    hA₀ hBA hr hw hu hweight hode hzero hjoin
  have hh := terminalCapInnerLift_weighted_bound hD hab.le hlam₀ (by positivity)
    (by norm_num : (0 : ℝ) ≤ 1) (terminalMorsePhysicalCutoff_smooth long A B s r) hu
    hcap hcover hcutoff hvalue hρ E weight hE hW hlocal
  exact hh.trans (mul_le_mul_of_nonneg_left
    (terminalCap_leading_normalization hA hj hs hscale ha (sub_nonneg.mpr hab.le) hdhi hlam) hW)

end ContinuousFlexibility.Radial
