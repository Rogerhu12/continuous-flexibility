import ContinuousFlexibility.Radial.OuterCoreMass

/-!
# The physical transition-core interval on either end

For a cell strictly after the initial cell, the core is precisely that
retained cell together with the glue preceding it in the outward order.
The endpoints below are in increasing physical radius on both ends.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

def morseOuterCoreLeft (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  if side then T.joinLeft side (n - 1) else T.radius side n (T.leftX side n)

def morseOuterCoreRight (T : MorseChainData) (side : Bool) (n : ℕ) : ℝ :=
  if side then T.radius side n (T.rightX side n) else T.joinRight side (n - 1)

theorem radialHilbertDensity_intervalIntegrable {D : ReferenceData}
    (hD : RadialProfileGeometry D) {l r : ℝ}
    (hl : l ∈ radialCore D) (hr : r ∈ radialCore D) :
    IntervalIntegrable (fun x => 12 * D.w x / x ^ 2) volume l r := by
  have hc : ContinuousOn (fun x => 12 * D.w x / x ^ 2) (radialCore D) :=
    (continuousOn_const.mul hD.2.2.1.1.continuous.continuousOn).div
      (continuousOn_id.pow 2)
      (fun x hx => (pow_pos (hD.1.trans hx.1) 2).ne')
  exact (hc.mono (ordConnected_Ioo.uIcc_subset hl hr)).intervalIntegrable

theorem radialHilbertIntervalMass_add {D : ReferenceData}
    (hD : RadialProfileGeometry D) {l c r : ℝ}
    (hl : l ∈ radialCore D) (hc : c ∈ radialCore D) (hr : r ∈ radialCore D) :
    radialHilbertIntervalMass D l r =
      radialHilbertIntervalMass D l c + radialHilbertIntervalMass D c r :=
  (intervalIntegral.integral_add_adjacent_intervals
    (radialHilbertDensity_intervalIntegrable hD hl hc)
    (radialHilbertDensity_intervalIntegrable hD hc hr)).symm

theorem morseRealized_retained_endpoints {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    T.radius side n (T.leftX side n) ∈ radialCore D ∧
      T.radius side n (T.rightX side n) ∈ radialCore D ∧
      T.radius side n (T.leftX side n) < T.radius side n (T.rightX side n) := by
  have hd := h.retained_data side n hn
  have horder := hd.2.2.2.1.trans hd.2.2.2.2.1
  have hl := left_mem_Icc.mpr horder.le
  have hr := right_mem_Icc.mpr horder.le
  exact ⟨h.radius_mem_core side n hn _ hl, h.radius_mem_core side n hn _ hr,
    h.radius_strictMonoOn side n hn hl hr horder⟩

/-- The definitions really are an ordered compact subinterval of the
physical annulus, for both outward orientations. -/
theorem morseOuterCore_interval {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index < n) :
    morseOuterCoreLeft T side n < morseOuterCoreRight T side n ∧
      Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) ⊆ radialCore D := by
  have hn₀ : T.index ≤ n - 1 := by omega
  have hn₁ : n - 1 + 1 = n := by omega
  have hends := morseRealized_retained_endpoints h side n hn.le
  have hprev := morseRealized_retained_endpoints h side (n - 1) hn₀
  have hj := h.join_data side (n - 1) hn₀
  cases side with
  | false =>
      have hjl : T.joinLeft false (n - 1) = T.radius false n (T.rightX false n) := by
        simpa only [Bool.false_eq_true, ite_false, hn₁] using hj.2.1
      have hjr : T.joinRight false (n - 1) =
          T.radius false (n - 1) (T.leftX false (n - 1)) := by
        simpa only [Bool.false_eq_true, ite_false] using hj.2.2.1
      change T.radius false n (T.leftX false n) < T.joinRight false (n - 1) ∧ _
      have hr : T.joinRight false (n - 1) ∈ radialCore D := hjr.symm ▸ hprev.1
      have hord : T.radius false n (T.leftX false n) < T.joinRight false (n - 1) :=
        hends.2.2.trans (hjl ▸ hj.1)
      exact ⟨hord, fun _ hx => ⟨hends.1.1.trans_le hx.1, hx.2.trans_lt hr.2⟩⟩
  | true =>
      have hjl : T.joinLeft true (n - 1) =
          T.radius true (n - 1) (T.rightX true (n - 1)) := by
        simpa only [ite_true] using hj.2.1
      have hjr : T.joinRight true (n - 1) = T.radius true n (T.leftX true n) := by
        simpa only [ite_true, hn₁] using hj.2.2.1
      change T.joinLeft true (n - 1) < T.radius true n (T.rightX true n) ∧ _
      have hl : T.joinLeft true (n - 1) ∈ radialCore D := hjl.symm ▸ hprev.2.1
      have hord : T.joinLeft true (n - 1) < T.radius true n (T.rightX true n) :=
        (hjr ▸ hj.1).trans hends.2.2
      exact ⟨hord, fun _ hx => ⟨hl.1.trans_le hx.1, hx.2.trans_lt hends.2.1.2⟩⟩

/-- Core mass is exactly retained-cell mass plus the mass of the preceding
glue; no part of the previous long positive cap is included. -/
theorem morseOuterCore_mass_eq {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index < n) :
    radialHilbertIntervalMass D (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) =
      radialHilbertIntervalMass D (T.radius side n (T.leftX side n))
        (T.radius side n (T.rightX side n)) +
      radialHilbertIntervalMass D (T.joinLeft side (n - 1)) (T.joinRight side (n - 1)) := by
  have hn₀ : T.index ≤ n - 1 := by omega
  have hn₁ : n - 1 + 1 = n := by omega
  have hends := morseRealized_retained_endpoints h side n hn.le
  have hprev := morseRealized_retained_endpoints h side (n - 1) hn₀
  have hj := h.join_data side (n - 1) hn₀
  cases side with
  | false =>
      have hjl : T.joinLeft false (n - 1) = T.radius false n (T.rightX false n) := by
        simpa only [Bool.false_eq_true, ite_false, hn₁] using hj.2.1
      have hjr : T.joinRight false (n - 1) =
          T.radius false (n - 1) (T.leftX false (n - 1)) := by
        simpa only [Bool.false_eq_true, ite_false] using hj.2.2.1
      have hr : T.joinRight false (n - 1) ∈ radialCore D := hjr.symm ▸ hprev.1
      change radialHilbertIntervalMass D (T.radius false n (T.leftX false n))
        (T.joinRight false (n - 1)) = _
      rw [radialHilbertIntervalMass_add h.geometry hends.1 hends.2.1 hr, hjl]
  | true =>
      have hjl : T.joinLeft true (n - 1) =
          T.radius true (n - 1) (T.rightX true (n - 1)) := by
        simpa only [ite_true] using hj.2.1
      have hjr : T.joinRight true (n - 1) = T.radius true n (T.leftX true n) := by
        simpa only [ite_true, hn₁] using hj.2.2.1
      have hl : T.joinLeft true (n - 1) ∈ radialCore D := hjl.symm ▸ hprev.2.1
      change radialHilbertIntervalMass D (T.joinLeft true (n - 1))
        (T.radius true n (T.rightX true n)) = _
      rw [radialHilbertIntervalMass_add h.geometry hl hends.1 hends.2.1, hjr, add_comm]

end ContinuousFlexibility.Radial
