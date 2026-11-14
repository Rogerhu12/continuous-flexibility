module

public import ContinuousFlexibility.Radial.TerminalMorseBoundarySlopeLower
public import ContinuousFlexibility.Radial.TerminalCapSourceEnergy

/-!
# The actual terminal Morse lift energy

The cap equation is transported onto its physical radius interval.
The constructed cutoff has its proved constant endpoint germs, so its
boundary energy is exactly the normalized outward slope of the same
stand-in. The remaining term is the actual positive cutoff integral.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open scoped Topology ContDiff

theorem terminalMorseCap_endpoints (long : Bool) (A B s : ℝ) (r : ℝ → ℝ) :
    terminalMorseLayerRadius long A B s r 0 =
      s * r (if long then morseRightTurn A B else morseCellLeftCut) ∧
    terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A) =
      s * r (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut) := by
  cases long <;> simp [terminalMorseLayerRadius, terminalMorseCapRadius,
    terminalMorseLayerOrigin, terminalMorseLayerLength, morseRightCapEnd, morseShortLeftCapLength]

theorem terminalMorseCap_radius_order (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r) :
    terminalMorseLayerRadius long A B s r 0 <
      terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL := terminalMorseLayerLength_pos long hA
  exact terminalMorseLayerRadius_strictMono long hB hAB hs hr
    ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL

theorem terminalMorseCap_preimage (long : Bool) {A B s z : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (hz : z ∈ Icc (terminalMorseLayerRadius long A B s r 0)
      (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A))) :
    ∃ t ∈ Icc 0 (terminalMorseLayerLength long A), terminalMorseLayerRadius long A B s r t = z := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL := terminalMorseLayerLength_pos long hA
  have hc : ContinuousOn (terminalMorseLayerRadius long A B s r)
      (Icc 0 (terminalMorseLayerLength long A)) :=
    (terminalMorseLayerRadius_smooth long A B s hr.smooth).continuous.continuousOn
  have hm := (terminalMorseLayerRadius_strictMono long hB hAB hs hr).monotoneOn
  have him := hc.image_Icc_of_monotoneOn hL.le hm
  have hmem : z ∈ terminalMorseLayerRadius long A B s r '' Icc 0 (terminalMorseLayerLength long A) := by
    rw [him]
    exact hz
  exact hmem

/-- The true positive profile and radius on the whole physical cap. -/
theorem terminalMorseCap_physical_coefficients (long : Bool)
    {A B s weightScale z : ℝ} {r w : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hscale : 0 < weightScale)
    (hA₀ : A ≤ 1 / 1000) (hr : IsNormalizedMorseCell A B r)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hz : z ∈ Icc (terminalMorseLayerRadius long A B s r 0)
      (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A))) :
    0 < z ∧ z ≤ 2 * s ∧ 0 < w z ∧ w z ≤ 7 * weightScale * s * A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  obtain ⟨t, ht, htz⟩ := terminalMorseCap_preimage long hB hAB hs hr hz
  have hx := terminalMorseLayer_point_mem long hB hAB ht
  have hvlo := terminalMorse_retained_speed_lower hr hx
  have hvhi := terminalMorse_retained_speed_upper hA hA₀ hr hx
  have hrhi := (terminalMorse_retained_radius_bounds hr hx).2
  have hzval : z = s * r (terminalMorseLayerOrigin long A B + t) := by
    simpa only [terminalMorseLayerRadius, terminalMorseCapRadius, one_mul] using htz.symm
  have hwval : w z = weightScale * (s * deriv r (terminalMorseLayerOrigin long A B + t)) := by
    rw [hzval]
    exact hweight _ hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← htz]
    exact terminalMorseLayerRadius_pos long hB hAB hs hr ht
  · rw [hzval]
    nlinarith only [mul_le_mul_of_nonneg_left hrhi hs.le]
  · rw [hwval]
    exact mul_pos hscale (mul_pos hs ((by positivity : 0 < A ^ 5 / 100).trans_le hvlo))
  · rw [hwval]
    nlinarith only [mul_le_mul_of_nonneg_left hvhi (mul_nonneg hscale.le hs.le)]

theorem terminalMorseCap_physical_equation (long : Bool)
    {A B j s : ℝ} {r w u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (hode : ∀ x ∈ Icc (if long then morseRightTurn A B else morseCellLeftCut)
        (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut),
      radialJacobi (j ^ 2) w u (s * r x) = 0) :
    ∀ z ∈ uIcc (terminalMorseLayerRadius long A B s r 0)
      (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)),
      radialJacobi (j ^ 2) w u z = 0 := by
  intro z hz
  rw [uIcc_of_le (terminalMorseCap_radius_order long hB hAB hs hr).le] at hz
  obtain ⟨t, ht, htz⟩ := terminalMorseCap_preimage long hB hAB hs hr hz
  rw [← htz]
  simpa only [terminalMorseLayerRadius, terminalMorseCapRadius, one_mul] using
    hode _ (terminalMorseLayer_cap_point_mem long ht)

theorem terminalMorseCap_cutoff_endpoints (long : Bool)
    {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r) :
    let R := terminalMorseLayerRadius long A B s r
    let L := terminalMorseLayerLength long A
    let χ := terminalMorsePhysicalCutoff long A B s r
    χ (R 0) = (if long then 0 else 1) ∧ χ (R L) = (if long then 1 else 0) ∧
      deriv χ (R 0) = 0 ∧ deriv χ (R L) = 0 := by
  have hj := terminalMorsePhysicalCutoff_join_germ long hB hAB hs hr
  have hc := terminalMorsePhysicalCutoff_wall_germ long hB hAB hs hr
  have hjd := hj.deriv_eq
  have hcd := hc.deriv_eq
  simp only [deriv_const] at hjd hcd
  cases long
  · exact ⟨hj.eq_of_nhds, hc.eq_of_nhds, hjd, hcd⟩
  · exact ⟨hc.eq_of_nhds, hj.eq_of_nhds, hcd, hjd⟩

/-- The same normalized cap lift has boundary flux exactly d. -/
theorem terminalMorseCapLift_energy_identity (long : Bool)
    {A B j s weightScale lam : ℝ} {r w u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hs : 0 < s)
    (hscale : 0 < weightScale) (hA₀ : A ≤ 1 / 1000)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hode : ∀ x ∈ Icc (if long then morseRightTurn A B else morseCellLeftCut)
        (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut),
      radialJacobi (j ^ 2) w u (s * r x) = 0)
    (hjoin : u (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) = 1)
    (hnorm : lam = standInBoundaryScale (j ^ 2)
      (w (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut))) :
    let R := terminalMorseLayerRadius long A B s r
    let L := terminalMorseLayerLength long A
    let χ := terminalMorsePhysicalCutoff long A B s r
    let d := standInBoundarySlope (if long then 1 else -1) (j ^ 2)
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) u
    (∫ z in R 0..R L, terminalCapEnergyDensity (j ^ 2) w (terminalCapLift lam χ u) z) =
      d + (∫ z in R 0..R L, terminalCapCutoffEnergy w χ u z) / lam := by
  let R := terminalMorseLayerRadius long A B s r
  let L := terminalMorseLayerLength long A
  let χ := terminalMorsePhysicalCutoff long A B s r
  let p := if long then R L else R 0
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hab : R 0 < R L := terminalMorseCap_radius_order long hB hAB hs hr
  have hpmem : p ∈ Icc (R 0) (R L) := by cases long <;> exact ⟨by simp [p, hab.le], by simp [p, hab.le]⟩
  have hpcoeff := terminalMorseCap_physical_coefficients long hB hAB hs hscale hA₀ hr hweight hpmem
  have hends := terminalMorseCap_endpoints long A B s r
  have hp : p = s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut) := by
    cases long
    · exact hends.1
    · exact hends.2
  have hup : u p = 1 := by rw [hp]; exact hjoin
  have hlamdef : lam = standInBoundaryScale (j ^ 2) (w p) p := by simpa only [hp] using hnorm
  have hlam : 0 < lam := by
    rw [hlamdef]
    exact standInBoundaryScale_pos (sq_pos_of_pos hj) hpcoeff.2.2.1 hpcoeff.1
  have hχ : χ (R 0) = (if long then 0 else 1) ∧
      χ (R L) = (if long then 1 else 0) ∧
      deriv χ (R 0) = 0 ∧ deriv χ (R L) = 0 :=
    terminalMorseCap_cutoff_endpoints long hB hAB hs hr
  have hflux : (terminalCapBoundaryFlux w χ u (R L) - terminalCapBoundaryFlux w χ u (R 0)) / lam =
      standInBoundarySlope (if long then 1 else -1) (j ^ 2) p u := by
    rw [standInBoundarySlope_eq_impedance (sq_pos_of_pos hj).ne' hpcoeff.2.2.1.ne'
      hpcoeff.1.ne' (by rw [hup]; exact one_ne_zero), hup, div_one, ← hlamdef]
    congr 1
    cases long <;> dsimp only [terminalCapBoundaryFlux]
    · rw [hχ.1, hχ.2.1]
      change 0 ^ 2 * u (R L) * (w (R L) * deriv u (R L)) -
        1 ^ 2 * u p * (w p * deriv u p) = (-1) * w p * deriv u p
      rw [hup]
      ring
    · rw [hχ.1, hχ.2.1]
      change 1 ^ 2 * u p * (w p * deriv u p) -
        0 ^ 2 * u (R 0) * (w (R 0) * deriv u (R 0)) = 1 * w p * deriv u p
      rw [hup]
      ring
  have henergy := terminalCapLift_energy_identity hlam hw
    (terminalMorsePhysicalCutoff_smooth long A B s r) hu
    (terminalMorseCap_physical_equation long hB hAB hs hr hode)
  rw [hflux, hp] at henergy
  exact henergy

/-- The actual Hilbert-density lift-source pairing is exactly the same
positive error appearing in the lift energy. -/
theorem terminalMorseCapLift_source_pairing (long : Bool)
    {A B s weightScale lam : ℝ} {r w u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hscale : 0 < weightScale)
    (hA₀ : A ≤ 1 / 1000) (hlam : 0 < lam)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x)) :
    let R := terminalMorseLayerRadius long A B s r
    let L := terminalMorseLayerLength long A
    let χ := terminalMorsePhysicalCutoff long A B s r
    (∫ z in R 0..R L, (12 * w z / z ^ 2) *
      terminalCapLift lam χ u z * terminalCapHilbertSource lam w χ u z) =
      (∫ z in R 0..R L, terminalCapCutoffEnergy w χ u z) / lam := by
  have hχ := terminalMorseCap_cutoff_endpoints long hB hAB hs hr
  have hc (z : ℝ) (hz : z ∈ uIcc (terminalMorseLayerRadius long A B s r 0)
      (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A))) := by
    rw [uIcc_of_le (terminalMorseCap_radius_order long hB hAB hs hr).le] at hz
    exact terminalMorseCap_physical_coefficients long hB hAB hs hscale hA₀ hr hweight hz
  exact terminalCapLift_source_density_pairing hlam hw
    (terminalMorsePhysicalCutoff_smooth long A B s r) hu hχ.2.2.1 hχ.2.2.2
    (fun z hz => (hc z hz).1.ne') (fun z hz => (hc z hz).2.2.1.ne')

end ContinuousFlexibility.Radial

