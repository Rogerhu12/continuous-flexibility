import ContinuousFlexibility.Radial.MorseRealizedConnectorBounds

/-!
# Splitting the resistance interval of a realized Morse chain

The resistance interval is the retained long cap followed by its
connector in increasing physical radius. The first left interval has
a zero-length connector. Positivity on the actual radial core provides
integrability of the inverse density and preserves the cap lower bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- The cap and its following connector exactly partition both physical
integrals. The connector adds nonnegative resistance, including when it
is the empty connector of the first left cap. -/
theorem morseRealizedJoin_integrals {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    morseJoinMass T D side n =
        (∫ x in morseChainMassEnd T side n..T.radius side n (T.rightX side n),
          D.w x * x ^ 6) +
        (∫ x in T.radius side n (T.rightX side n)..morseChainResistanceEnd T side n,
          D.w x * x ^ 6) ∧
      morseJoinResistance T D side n =
        (∫ x in morseChainMassEnd T side n..T.radius side n (T.rightX side n),
          (D.w x * x ^ 8)⁻¹) +
        (∫ x in T.radius side n (T.rightX side n)..morseChainResistanceEnd T side n,
          (D.w x * x ^ 8)⁻¹) ∧
      0 ≤ ∫ x in T.radius side n (T.rightX side n)..morseChainResistanceEnd T side n,
        (D.w x * x ^ 8)⁻¹ := by
  let b := morseChainMassEnd T side n
  let e := T.radius side n (T.rightX side n)
  let d := morseChainResistanceEnd T side n
  have hret := h.retained_data side n hn
  have hlt : T.leftX side n < morseChainRightTurn T n := hret.2.2.2.1
  have htr : morseChainRightTurn T n < T.rightX side n := hret.2.2.2.2.1
  have ht : morseChainRightTurn T n ∈ Icc (T.leftX side n) (T.rightX side n) :=
    ⟨hlt.le, htr.le⟩
  have hr : T.rightX side n ∈ Icc (T.leftX side n) (T.rightX side n) :=
    right_mem_Icc.mpr (hlt.trans htr).le
  have hbe : b ≤ e :=
    (h.radius_strictMonoOn side n hn).monotoneOn ht hr htr.le
  have hbcore : b ∈ radialCore D := h.radius_mem_core side n hn _ ht
  have hecore : e ∈ radialCore D := h.radius_mem_core side n hn _ hr
  have hEnd : e ≤ d ∧ d ∈ radialCore D := by
    rcases morseRealizedConnector_join_or_zero h side n hn with heq |
      ⟨k, hk, hl, hd, _⟩
    · refine ⟨le_of_eq heq, ?_⟩
      change morseChainResistanceEnd T side n ∈ radialCore D
      rw [← heq]
      exact hecore
    · have hj := h.join_data side k hk
      obtain ⟨_, hm, _, _, hright, _⟩ := morseRealizedJoin_endpoints h side k hk
      have hretm := h.retained_data side (if side then k + 1 else k) hm
      have horder : T.leftX side (if side then k + 1 else k) ≤
          T.rightX side (if side then k + 1 else k) :=
        (hretm.2.2.2.1.trans hretm.2.2.2.2.1).le
      constructor
      · change T.radius side n (T.rightX side n) ≤ morseChainResistanceEnd T side n
        rw [hl, hd]
        exact hj.1.le
      · change morseChainResistanceEnd T side n ∈ radialCore D
        rw [hd, hright]
        exact h.radius_mem_core side (if side then k + 1 else k) hm _
          (left_mem_Icc.mpr horder)
  have hwhole : Icc b d ⊆ radialCore D := fun x hx =>
    ⟨hbcore.1.trans_le hx.1, hx.2.trans_lt hEnd.2.2⟩
  have hwp (x : ℝ) (hx : x ∈ Icc b d) : 0 < D.w x :=
    h.geometry.2.2.2.2.1 x (hwhole hx)
  have hxp (x : ℝ) (hx : x ∈ Icc b d) : 0 < x :=
    h.geometry.1.trans (hwhole hx).1
  have hw : ContDiff ℝ ∞ D.w := h.geometry.2.2.1.1
  have hMc : Continuous (fun x => D.w x * x ^ 6) :=
    hw.continuous.mul (continuous_id.pow 6)
  have hRc : ContinuousOn (fun x => (D.w x * x ^ 8)⁻¹) (Icc b d) :=
    (hw.continuous.continuousOn.mul (continuous_id.continuousOn.pow 8)).inv₀
      (fun x hx => (mul_pos (hwp x hx) (pow_pos (hxp x hx) 8)).ne')
  have hM := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hMc.intervalIntegrable b e) (hMc.intervalIntegrable e d)
  have hR := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hRc.mono (fun _ hx => ⟨hx.1, hx.2.trans hEnd.1⟩)).intervalIntegrable_of_Icc hbe)
    ((hRc.mono (fun _ hx => ⟨hbe.trans hx.1, hx.2⟩)).intervalIntegrable_of_Icc hEnd.1)
  change (∫ x in b..d, D.w x * x ^ 6) =
      (∫ x in b..e, D.w x * x ^ 6) + (∫ x in e..d, D.w x * x ^ 6) ∧
    (∫ x in b..d, (D.w x * x ^ 8)⁻¹) =
      (∫ x in b..e, (D.w x * x ^ 8)⁻¹) + (∫ x in e..d, (D.w x * x ^ 8)⁻¹) ∧
    0 ≤ ∫ x in e..d, (D.w x * x ^ 8)⁻¹
  refine ⟨hM.symm, hR.symm, ?_⟩
  exact intervalIntegral.integral_nonneg hEnd.1 (fun x hx =>
    inv_nonneg.mpr (mul_nonneg (hwp x ⟨hbe.trans hx.1, hx.2⟩).le
      (pow_nonneg (hxp x ⟨hbe.trans hx.1, hx.2⟩).le 8)))

end ContinuousFlexibility.Radial
