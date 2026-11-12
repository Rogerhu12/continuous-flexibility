import ContinuousFlexibility.Radial.TerminalMorseLiftEnergy
import ContinuousFlexibility.Radial.TerminalMorseSourceBudget

/-!
# Fixed coefficient powers in the actual lift-energy error

The actual normalization removes profile height and radius scale.
The same stand-in slope lower bound removes the remaining inverse
frequency square, leaving a seventeenth inverse power of A. The two
attenuation factors come directly from the square of the same solution.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff

theorem terminalCap_normalized_energy_budget {A j s k lam width length d K : ℝ}
    (hA : 0 < A) (hj : 0 < j) (hs : 0 < s) (hk : 0 < k) (hK : 0 ≤ K)
    (hwidth : s * A ^ 5 / 2400 ≤ width) (hlength : length ≤ 2 * s)
    (hlam : j ^ 2 * k * A ^ 5 / 200 ≤ lam)
    (hd : A ^ 3 / (14 * j ^ 2) ≤ d) :
    (length * (7 * k * s * A) * (K / width) ^ 2 * 4 / lam) ≤
      1000000000000 * (1 + K) ^ 2 * d / A ^ 17 := by
  have hwpos : 0 < width := (by positivity : 0 < s * A ^ 5 / 2400).trans_le hwidth
  have hlampos : 0 < lam := (by positivity : 0 < j ^ 2 * k * A ^ 5 / 200).trans_le hlam
  have hdpos : 0 < d := (by positivity : 0 < A ^ 3 / (14 * j ^ 2)).trans_le hd
  have hc : K / width ≤ 2400 * K / (s * A ^ 5) := by
    calc
      _ ≤ K / (s * A ^ 5 / 2400) :=
        div_le_div_of_nonneg_left hK (by positivity) hwidth
      _ = _ := by field_simp [hs.ne', hA.ne'] <;> ring
  have hcsq : (K / width) ^ 2 ≤ (2400 * K / (s * A ^ 5)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hc
  have hnum : length * (7 * k * s * A) * (K / width) ^ 2 * 4 ≤
      (2 * s) * (7 * k * s * A) * (2400 * K / (s * A ^ 5)) ^ 2 * 4 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_right hlength (by positivity)) hcsq
        (sq_nonneg _) (by positivity)) (by norm_num)
  have hinvj : 1 / j ^ 2 ≤ 14 * d / A ^ 3 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hj) (pow_pos hA 3)).mpr
    have h := (div_le_iff₀ (by positivity : 0 < 14 * j ^ 2)).mp hd
    nlinarith only [h]
  calc
    _ ≤ ((2 * s) * (7 * k * s * A) * (2400 * K / (s * A ^ 5)) ^ 2 * 4) / lam :=
      div_le_div_of_nonneg_right hnum hlampos.le
    _ ≤ ((2 * s) * (7 * k * s * A) * (2400 * K / (s * A ^ 5)) ^ 2 * 4) /
        (j ^ 2 * k * A ^ 5 / 200) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlam
    _ = (64512000000 * K ^ 2 / A ^ 14) * (1 / j ^ 2) := by
      field_simp [hs.ne', hk.ne', hj.ne', hA.ne'] <;> ring
    _ ≤ (64512000000 * K ^ 2 / A ^ 14) * (14 * d / A ^ 3) :=
      mul_le_mul_of_nonneg_left hinvj (by positivity)
    _ = 903168000000 * K ^ 2 * d / A ^ 17 := by
      field_simp [hA.ne'] <;> ring
    _ ≤ _ := by
      have hsq : K ^ 2 ≤ (1 + K) ^ 2 := by nlinarith only [hK]
      have hcoef : 903168000000 * K ^ 2 ≤ 1000000000000 * (1 + K) ^ 2 := by
        nlinarith only [hsq, sq_nonneg K]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hdpos.le)
        (pow_nonneg hA.le 17)

def terminalMorseEnergyErrorConstant : ℝ :=
  1000000000000 * (1 + terminalPhysicalCutoffJetConstant 1) ^ 2

theorem terminalMorseEnergyErrorConstant_pos : 0 < terminalMorseEnergyErrorConstant := by
  have h := terminalPhysicalCutoffJetConstant_nonneg 1
  unfold terminalMorseEnergyErrorConstant
  positivity

def terminalMorseEnergyErrorExponent : ℝ :=
  terminalMorsePolynomialExponent terminalMorseEnergyErrorConstant 17

theorem terminalMorseEnergyErrorExponent_pos : 0 < terminalMorseEnergyErrorExponent := by
  unfold terminalMorseEnergyErrorExponent terminalMorsePolynomialExponent
  positivity

/-- The actual diagonal lift-energy error has two attenuation factors
and a fixed coefficient power, relative to the same normalized slope d. -/
theorem terminalMorseCapLift_energy_error_radialE (T : Statements.MorseChainData)
    (long : Bool) (m n : ℕ) {B j s weightScale lam : ℝ} {r w u : ℝ → ℝ}
    (hd : T.d m = morseChainInteger m) (hmn : m ≤ n) (hn : 1 ≤ n)
    (hB : 0 < B) (hAB : 4 * B < Statements.morseChainA T m) (hj : 0 < j) (hs : 0 < s)
    (hscale : 0 < weightScale) (hA₀ : Statements.morseChainA T m ≤ 1 / 1000)
    (hBAlo : (Statements.morseChainA T m) ^ 9 / (9 : ℝ) ^ 9 ≤ B)
    (hBAhi : B ≤ (Statements.morseChainA T m) ^ 9)
    (hr : IsNormalizedMorseCell (Statements.morseChainA T m) B r)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd (Statements.morseChainA T m) B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hode : ∀ x ∈ Icc (if long then morseRightTurn (Statements.morseChainA T m) B else morseCellLeftCut)
        (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseShortLeftCapCut),
      radialJacobi (j ^ 2) w u (s * r x) = 0)
    (hzero : u (s * r (if long then morseRightTurn (Statements.morseChainA T m) B else morseShortLeftCapCut)) = 0)
    (hjoin : u (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut)) = 1)
    (hinit : long = true → 0 < deriv u (s * r (morseRightTurn (Statements.morseChainA T m) B)))
    (haction : 1000000000 ≤ j * sqrt (Statements.morseChainA T m))
    (hnorm : lam = standInBoundaryScale (j ^ 2)
      (w (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut)))
      (s * r (if long then morseRightCapEnd (Statements.morseChainA T m) B (1 / 100) else morseCellLeftCut))) :
    let A := Statements.morseChainA T m
    let R := terminalMorseLayerRadius long A B s r
    let L := terminalMorseLayerLength long A
    let χ := terminalMorsePhysicalCutoff long A B s r
    let d := standInBoundarySlope (if long then 1 else -1) (j ^ 2)
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) u
    let error := (∫ z in R 0..R L, terminalCapCutoffEnergy w χ u z) / lam
    0 ≤ error ∧
      error ≤ d * Statements.radialE n ^ terminalMorseEnergyErrorExponent *
        exp (-2 * (j * sqrt A / 50000000)) ∧
      |(∫ z in R 0..R L, terminalCapEnergyDensity (j ^ 2) w (terminalCapLift lam χ u) z) - d| ≤
        d * Statements.radialE n ^ terminalMorseEnergyErrorExponent *
          exp (-2 * (j * sqrt A / 50000000)) := by
  let A := Statements.morseChainA T m
  let R := terminalMorseLayerRadius long A B s r
  let L := terminalMorseLayerLength long A
  let χ := terminalMorsePhysicalCutoff long A B s r
  let d := standInBoundarySlope (if long then 1 else -1) (j ^ 2)
    (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) u
  let width := terminalMorseLayerRight long A B s r - terminalMorseLayerLeft long A B s r
  let W := 7 * weightScale * s * A
  let C := terminalPhysicalCutoffJetConstant 1 / width
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hab : R 0 < R L := terminalMorseCap_radius_order long hB hAB hs hr
  have hcoeff (z : ℝ) (hz : z ∈ Icc (R 0) (R L)) :=
    terminalMorseCap_physical_coefficients long hB hAB hs hscale hA₀ hr hweight hz
  have hcapwidth : R L - R 0 ≤ 2 * s := by
    have hleft := (hcoeff (R 0) ⟨le_rfl, hab.le⟩).1
    have hright := (hcoeff (R L) ⟨hab.le, le_rfl⟩).2.1
    linarith only [hleft, hright]
  have hcut (z : ℝ) (_ : z ∈ Icc (R 0) (R L)) : |deriv χ z| ≤ C :=
    terminalPhysicalCutoff_deriv_bound long (terminalMorseLayer_order long hB hAB hs hr) z
  have hval (z : ℝ) (_ : z ∈ Icc (R 0) (R L)) (hz : deriv χ z ≠ 0) :
      |u z| ≤ 2 * exp (-(j * sqrt A / 50000000)) := by
    have hzlayer := terminalMorsePhysicalCutoff_tsupport_deriv long hB hAB hs hr (subset_tsupport _ hz)
    exact (terminalMorse_physical_layer_jets long hB hAB hj hs hscale.ne' hA₀ hBAlo hBAhi
      hr hw hu hweight hode hzero hjoin hinit haction hzlayer).1
  obtain ⟨hpos, hbound⟩ := terminalCapCutoffEnergy_integral_bound
    (a := R 0) (b := R L) (W := W) (C := C) (A := 2) (σ := j * sqrt A / 50000000)
    hab.le (by dsimp only [W]; positivity) hw (terminalMorsePhysicalCutoff_smooth long A B s r) hu
    (fun z hz => ⟨(hcoeff z hz).2.2.1.le, (hcoeff z hz).2.2.2⟩) hcut hval
  have hlamlo := terminalMorse_boundary_normalization_lower long hB hAB hs hscale hr hweight hnorm
  have hlam : 0 < lam := (by positivity : 0 < j ^ 2 * weightScale * A ^ 5 / 200).trans_le hlamlo
  have hslope : A ^ 3 / (14 * j ^ 2) ≤ d :=
    terminalMorse_standIn_slope_lower long hB hAB hj hs hscale.ne' hA₀ hr hw hu hweight hode hzero hjoin
  have hdpos : 0 < d := (by positivity : 0 < A ^ 3 / (14 * j ^ 2)).trans_le hslope
  have hcost := terminalCap_normalized_energy_budget hA hj hs hscale
    (terminalPhysicalCutoffJetConstant_nonneg 1)
    (terminalMorseLayer_coarse_geometry long hB hAB hs hA₀ hr).2.1 hcapwidth hlamlo hslope
  have hbudget := terminalMorse_polynomial_le_radialE T terminalMorseEnergyErrorConstant_pos
    17 m n hd hmn hn
  have hcostE : ((R L - R 0) * W * C ^ 2 * (2 : ℝ) ^ 2 / lam) ≤
      d * Statements.radialE n ^ terminalMorseEnergyErrorExponent := by
    calc
      _ ≤ terminalMorseEnergyErrorConstant * d / A ^ 17 := by
        simpa only [W, C, width, terminalMorseEnergyErrorConstant, show (2 : ℝ) ^ 2 = 4 by norm_num] using hcost
      _ = d * (terminalMorseEnergyErrorConstant / A ^ 17) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hdpos.le
  have herrorpos : 0 ≤ (∫ z in R 0..R L, terminalCapCutoffEnergy w χ u z) / lam :=
    div_nonneg hpos hlam.le
  have herror :
      (∫ z in R 0..R L, terminalCapCutoffEnergy w χ u z) / lam ≤
        d * Statements.radialE n ^ terminalMorseEnergyErrorExponent * exp (-2 * (j * sqrt A / 50000000)) := by
    calc
      _ ≤ ((R L - R 0) * W * C ^ 2 * (2 : ℝ) ^ 2 *
          exp (-2 * (j * sqrt A / 50000000))) / lam :=
        div_le_div_of_nonneg_right hbound hlam.le
      _ = (((R L - R 0) * W * C ^ 2 * (2 : ℝ) ^ 2) / lam) *
          exp (-2 * (j * sqrt A / 50000000)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcostE (exp_pos _).le
  refine ⟨herrorpos, herror, ?_⟩
  rw [terminalMorseCapLift_energy_identity long hB hAB hj hs hscale hA₀ hr hw hu hweight hode hjoin hnorm,
    add_sub_cancel_left, abs_of_nonneg herrorpos]
  exact herror

end ContinuousFlexibility.Radial

