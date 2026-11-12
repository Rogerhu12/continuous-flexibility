import ContinuousFlexibility.Radial.TerminalMorseProfileJets
import ContinuousFlexibility.Radial.TerminalCapLayerL2

/-!
# The actual terminal Morse cutoff source in weighted L²

This is the quantitative source estimate for the constructed physical
cutoff and the same normalized stand-in solution. Potential, solution,
profile, cutoff, support, and measure estimates are all supplied by the
actual Morse construction and the preceding proved lemmas.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff ENNReal

/-- The explicit coefficient cost, separated from the cap exponential. -/
def terminalMorseCapSourcePrefactor (long : Bool) (A B j s weightScale lam : ℝ)
    (r : ℝ → ℝ) : ℝ :=
  let a := terminalMorseLayerLeft long A B s r
  let b := terminalMorseLayerRight long A B s r
  let W := 7 * weightScale * s * A
  let W₁ := (2 * weightScale * s * A) / (s * A ^ 5 / 100)
  let C₁ := terminalPhysicalCutoffJetConstant 1 / (b - a)
  let C₂ := terminalPhysicalCutoffJetConstant 2 / (b - a) ^ 2
  let R := (2 * s) ^ 2 / (12 * (weightScale * (s * A ^ 5 / 100)))
  let U₁ := 600 * j * sqrt A / (s * A ^ 5)
  R * ((2 * W * C₁ * U₁ + (W₁ * C₁ + W * C₂) * 2) / sqrt lam) *
    sqrt ((12 * W / a ^ 2) * (b - a))

theorem terminalMorseCapSourcePrefactor_nonneg (long : Bool) {A B j s weightScale lam : ℝ}
    {r : ℝ → ℝ} (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 ≤ j) (hs : 0 < s)
    (hscale : 0 ≤ weightScale) (hr : IsNormalizedMorseCell A B r) :
    0 ≤ terminalMorseCapSourcePrefactor long A B j s weightScale lam r := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hwidth := sub_pos.mpr (terminalMorseLayer_order long hB hAB hs hr)
  have hC₁ := terminalPhysicalCutoffJetConstant_nonneg 1
  have hC₂ := terminalPhysicalCutoffJetConstant_nonneg 2
  dsimp only [terminalMorseCapSourcePrefactor]
  positivity

/-- The actual cutoff residual is an L² source with a genuine
exponentially small norm. No coefficient or cutoff jet bound is an input. -/
theorem terminalMorse_cutoff_source_L2 (D : Statements.ReferenceData) (long : Bool)
    {A B j s weightScale lam : ℝ} {r u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hs : 0 < s)
    (hscale : 0 < weightScale) (hlam : 0 < lam)
    (hA₀ : A ≤ 1 / 1000) (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ D.w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      D.w (s * r x) = weightScale * (s * deriv r x))
    (hode : ∀ x ∈ Icc (if long then morseRightTurn A B else morseCellLeftCut)
        (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut),
      radialJacobi (j ^ 2) D.w u (s * r x) = 0)
    (hzero : u (s * r (if long then morseRightTurn A B else morseShortLeftCapCut)) = 0)
    (hjoin : u (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) = 1)
    (hinit : long = true → 0 < deriv u (s * r (morseRightTurn A B)))
    (haction : 1000000000 ≤ j * sqrt A) :
    MemLp (terminalCapHilbertSource lam D.w (terminalMorsePhysicalCutoff long A B s r) u)
      2 (Statements.radialHilbertMeasure D) ∧
      eLpNorm (terminalCapHilbertSource lam D.w (terminalMorsePhysicalCutoff long A B s r) u)
        2 (Statements.radialHilbertMeasure D) ≤
        ENNReal.ofReal (terminalMorseCapSourcePrefactor long A B j s weightScale lam r *
          exp (-(j * sqrt A / 50000000))) := by
  let a := terminalMorseLayerLeft long A B s r
  let b := terminalMorseLayerRight long A B s r
  let W := 7 * weightScale * s * A
  let W₁ := (2 * weightScale * s * A) / (s * A ^ 5 / 100)
  let C₁ := terminalPhysicalCutoffJetConstant 1 / (b - a)
  let C₂ := terminalPhysicalCutoffJetConstant 2 / (b - a) ^ 2
  let R := (2 * s) ^ 2 / (12 * (weightScale * (s * A ^ 5 / 100)))
  let U₁ := 600 * j * sqrt A / (s * A ^ 5)
  let sigma := j * sqrt A / 50000000
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have ha : 0 < a := terminalMorseLayerLeft_pos long hB hAB hs hr
  have hab : a < b := terminalMorseLayer_order long hB hAB hs hr
  have hcoeff (z : ℝ) (hz : z ∈ Icc a b) :=
    terminalMorse_physical_layer_coefficients long hB hAB hs hscale hA₀ hBAhi hr hw hweight hz
  have hjets (z : ℝ) (hz : z ∈ Icc a b) :=
    terminalMorse_physical_layer_jets long hB hAB hj hs hscale.ne' hA₀ hBAlo hBAhi
      hr hw hu hweight hode hzero hjoin hinit haction hz
  have hcut₁ (z : ℝ) (_ : z ∈ Icc a b) :
      |deriv (terminalMorsePhysicalCutoff long A B s r) z| ≤ C₁ :=
    terminalPhysicalCutoff_deriv_bound long hab z
  have hcut₂ (z : ℝ) (_ : z ∈ Icc a b) :
      |deriv (deriv (terminalMorsePhysicalCutoff long A B s r)) z| ≤ C₂ :=
    terminalPhysicalCutoff_second_bound long hab z
  obtain ⟨hmem, hnorm⟩ := terminalCapHilbertSource_layer_L2 D
    (a := a) (b := b) (lam := lam) (R := R) (W := W) (W₁ := W₁) (C₁ := C₁) (C₂ := C₂)
    (A := 2) (B := U₁) (σ := sigma)
    ha hab.le hlam (by norm_num) (by dsimp only [U₁]; positivity)
    hw (terminalMorsePhysicalCutoff_smooth long A B s r) hu
    (fun z hz => (hcoeff z hz).1.ne')
    (terminalMorsePhysicalCutoff_tsupport_deriv long hB hAB hs hr)
    (fun z hz => (hcoeff z hz).2.2.2)
    (fun z hz => (hcoeff z hz).2.1)
    (fun z hz => (hcoeff z hz).2.2.1)
    hcut₁ hcut₂ (fun z hz => (hjets z hz).1) (fun z hz => (hjets z hz).2)
  refine ⟨hmem, hnorm.trans_eq ?_⟩
  congr 1
  dsimp only [terminalMorseCapSourcePrefactor, terminalCapSourceEnvelope,
    a, b, W, W₁, C₁, C₂, R, U₁, sigma]
  ring

/-- The same constructed cutoff satisfies the actual differential
equation with that Hilbert source on the retained cell. -/
theorem terminalMorse_cutoff_weighted_equation (long : Bool) {A B j s weightScale lam x : ℝ}
    {r w u : ℝ → ℝ} (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hscale : 0 < weightScale) (hr : IsNormalizedMorseCell A B r)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ y ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r y) = weightScale * (s * deriv r y))
    (hode : ∀ y ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      radialJacobi (j ^ 2) w u (s * r y) = 0)
    (hx : x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :
    radialJacobi (j ^ 2) w (terminalCapLift lam (terminalMorsePhysicalCutoff long A B s r) u)
        (s * r x) =
      -(12 * w (s * r x) / (s * r x) ^ 2) *
        terminalCapHilbertSource lam w (terminalMorsePhysicalCutoff long A B s r) u (s * r x) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hrad : 0 < s * r x := mul_pos hs (terminalMorse_retained_radius_bounds hr hx).1
  have hv : 0 < deriv r x := (by positivity : 0 < A ^ 5 / 100).trans_le
    (terminalMorse_retained_speed_lower hr hx)
  have hwp : 0 < w (s * r x) := by
    rw [hweight x hx]
    exact mul_pos hscale (mul_pos hs hv)
  exact terminalCapLift_weighted_equation (lam := lam) hw
    (terminalMorsePhysicalCutoff_smooth long A B s r) hu hrad.ne' hwp.ne' (hode x hx)

/-- Actual placement of the true border on the opposite side makes the
scalar pairing vanish for this very cutoff lift. -/
theorem terminalMorse_cutoff_scalar_pairing_zero (D : Statements.ReferenceData) (long : Bool)
    {A B s lam : ℝ} {r u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (hborder : Function.support (Statements.referenceColumn D) ⊆
      if long then Iic (terminalMorseLayerLeft long A B s r)
      else Ici (terminalMorseLayerRight long A B s r)) :
    (∫ z in D.a..D.b, Statements.referenceColumn D z *
      terminalCapLift lam (terminalMorsePhysicalCutoff long A B s r) u z) = 0 := by
  apply terminalCapLift_scalar_pairing_zero D lam
  apply Set.disjoint_left.mpr
  intro z hz hzcut
  have hcut := terminalPhysicalCutoff_support long (terminalMorseLayer_order long hB hAB hs hr) hzcut
  have hb := hborder hz
  cases long
  · change z < terminalMorseLayerRight false A B s r at hcut
    change terminalMorseLayerRight false A B s r ≤ z at hb
    exact (not_lt_of_ge hb) hcut
  · change terminalMorseLayerLeft true A B s r < z at hcut
    change z ≤ terminalMorseLayerLeft true A B s r at hb
    exact (not_lt_of_ge hb) hcut

end ContinuousFlexibility.Radial

