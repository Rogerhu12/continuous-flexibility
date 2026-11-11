import ContinuousFlexibility.Radial.MorseSecondModeNaturalTransport
import ContinuousFlexibility.Radial.TailNaturalUniqueness
import ContinuousFlexibility.Radial.DeepTailPhysicalBounds
import ContinuousFlexibility.Radial.SeedTailFlatExtension

/-!
# Endpoint flatness of the specified second-mode natural solution

The actual Morse tail supplies deep data after a finite discard. The
concrete natural-line and physical-flatness proofs then transfer a smooth
flat representative to the original solution on an unchanged endpoint germ.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem morseSecondMode_entrance_radius {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {N : ℕ}
    (hreal : MorseChainRealization T σ D C) (hN : T.index < N) (right : Bool) :
    tailPhysicalRadius right (morseSecondModeTail D T N right).entrance =
      morseSecondModeMassLeft T right (if right then N else N - 1) := by
  have hD := morseSecondMode_profileGeometry hreal
  have hi : T.index ≤ (if right then N else N - 1) := by
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hp := hD.1.trans (morseSecondMode_massEndpoints hreal right hi).1.1
  cases right <;>
    simp only [tailPhysicalRadius, morseSecondModeTail, Bool.false_eq_true,
      ↓reduceIte, neg_neg] at hp ⊢ <;> exact exp_log hp

theorem morseSecondMode_entrance_radius_tendsto {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (right : Bool) :
    Tendsto (fun N : ℕ =>
      tailPhysicalRadius right (morseSecondModeTail D T N right).entrance)
      atTop (𝓝 (if right then D.b else D.a)) := by
  obtain ⟨_, _, _, _, _, _, hends, _, _, _⟩ := hreal
  have hpred : Tendsto (fun N : ℕ => N - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    omega
  have hlim : Tendsto
      (fun N : ℕ => morseSecondModeMassLeft T right (if right then N else N - 1))
      atTop (𝓝 (if right then D.b else D.a)) := by
    cases right
    · exact (hends false).1.comp hpred
    · exact (hends true).1
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop T.index] with N hN
  exact (morseSecondMode_entrance_radius hreal hN right).symm

/-- The physical entrance eventually lies strictly beyond any fixed
interior entry in the outward direction. -/
theorem morseSecondMode_eventually_beyond_entry {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {entry : ℝ}
    (hreal : MorseChainRealization T σ D C) (hentry : entry ∈ radialCore D)
    (right : Bool) :
    ∀ᶠ N : ℕ in atTop, T.index < N ∧
      tailPhysicalRadius right (morseSecondModeTail D T N right).entrance ∈
        radialTailInterval D right entry := by
  have hlim := morseSecondMode_entrance_radius_tendsto hreal right
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at hlim
    filter_upwards [eventually_gt_atTop T.index,
      hlim.eventually (eventually_lt_nhds hentry.1)] with N hN hx
    have hc := morseSecondMode_radius_mem_core hreal hN false
      ⟨le_rfl, (morseSecondMode_entrance_order hreal hN false).1⟩
    exact ⟨hN, hc.1, hx⟩
  · simp only [↓reduceIte] at hlim
    filter_upwards [eventually_gt_atTop T.index,
      hlim.eventually (eventually_gt_nhds hentry.2)] with N hN hx
    have hc := morseSecondMode_radius_mem_core hreal hN true
      ⟨le_rfl, (morseSecondMode_entrance_order hreal hN true).1⟩
    exact ⟨hN, hx, hc.2⟩

theorem morseSecondMode_tailInterval_subset_core {D : ReferenceData}
    {entry : ℝ} (hentry : entry ∈ radialCore D) (right : Bool) :
    radialTailInterval D right entry ⊆ radialCore D := by
  cases right
  · intro r hr
    exact ⟨hr.1, hr.2.trans hentry.2⟩
  · intro r hr
    exact ⟨hentry.1.trans hr.1, hr.2⟩

theorem morseSecondMode_log_mem {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {N : ℕ} {r : ℝ}
    (hreal : MorseChainRealization T σ D C) (hN : T.index < N) (right : Bool)
    (hr : r ∈ radialTailInterval D right
      (tailPhysicalRadius right (morseSecondModeTail D T N right).entrance)) :
    tailPhysicalLog right r ∈ Ioo (morseSecondModeTail D T N right).entrance
      (morseSecondModeTail D T N right).endpoint := by
  have hD := morseSecondMode_profileGeometry hreal
  have hc := morseSecondMode_radius_mem_core hreal hN right
    ⟨le_rfl, (morseSecondMode_entrance_order hreal hN right).1⟩
  have hrpos := hD.1.trans ((morseSecondMode_tailInterval_subset_core hc right) hr).1
  have hcpos := tailPhysicalRadius_pos right (morseSecondModeTail D T N right).entrance
  have he := (tailPhysicalLog_radius right (morseSecondModeTail D T N right).entrance).symm
  cases right
  · change D.a < r ∧ r < tailPhysicalRadius false
      (morseSecondModeTail D T N false).entrance at hr
    change (morseSecondModeTail D T N false).entrance = -log
      (tailPhysicalRadius false (morseSecondModeTail D T N false).entrance) at he
    change (morseSecondModeTail D T N false).entrance < -log r ∧ -log r < -log D.a
    rw [he]
    exact ⟨neg_lt_neg (log_lt_log hrpos hr.2),
      neg_lt_neg (log_lt_log hD.1 hr.1)⟩
  · change tailPhysicalRadius true
      (morseSecondModeTail D T N true).entrance < r ∧ r < D.b at hr
    change (morseSecondModeTail D T N true).entrance = log
      (tailPhysicalRadius true (morseSecondModeTail D T N true).entrance) at he
    change (morseSecondModeTail D T N true).entrance < log r ∧ log r < log D.b
    rw [he]
    exact ⟨log_lt_log hcpos hr.1, log_lt_log hrpos hr.2⟩

/-- Endpoint-flat smooth germ of the original specified natural solution.
No new hypothesis about the R06 blueprint node is introduced. -/
theorem morseSecondMode_naturalTail_flatGerm {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {right : Bool} {entry : ℝ} {u : ℝ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hentry : entry ∈ radialCore D) (hu : RadialNaturalTail D right 2 entry u) :
    ∃ c : ℝ, c ∈ radialTailInterval D right entry ∧ c ∈ radialCore D ∧
      ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
        (∀ r ∈ radialTailInterval D right c, v r = u r) ∧
        ∀ s : ℕ, radialJet s v (if right then D.b else D.a) = 0 := by
  obtain ⟨N, hN, hdeep⟩ := morseSecondMode_exists_physicalDeepTail hreal hmass hσ
  obtain ⟨M, hM, hMc⟩ := ((eventually_ge_atTop N).and
    (morseSecondMode_eventually_beyond_entry hreal hentry right)).exists
  obtain ⟨hT, hphysical⟩ := hdeep M hM right
  have hV := morseSecondModePullback_naturalEquation hreal hMc.1 hphysical hentry hMc.2 hu
  have hline := tailNaturalLineAndKernel hT
    (by norm_num [morseSecondModeTail]) (by norm_num [morseSecondModeTail])
  have hDacc : IsAccumulatingProfile D := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hacc⟩ := hreal
    exact ⟨C, hacc⟩
  have hflat := tailPhysicalFlatConclusion_of_natural_line hDacc hT hphysical
    (by norm_num [morseSecondModeTail]) hline
  obtain ⟨v, hv, heq, hjets⟩ := tailPhysicalFlatExtension_of_naturalEquation hline hflat hV
  let c := tailPhysicalRadius right (morseSecondModeTail D T M right).entrance
  have hc : c ∈ radialCore D := morseSecondMode_radius_mem_core hreal hMc.1 right
    ⟨le_rfl, (morseSecondMode_entrance_order hreal hMc.1 right).1⟩
  refine ⟨c, hMc.2, hc, v, hv, ?_, hjets⟩
  intro r hr
  have hrpos := (morseSecondMode_profileGeometry hreal).1.trans
    ((morseSecondMode_tailInterval_subset_core hc right) hr).1
  have hx := morseSecondMode_log_mem hreal hMc.1 right hr
  have hh := heq (tailPhysicalLog right r) hx
  have hrel := morseSecondModePullback_relation (morseSecondMode_profileGeometry hreal)
    right u (tailPhysicalLog right r)
  rw [tailPhysicalRadius_log right hrpos] at hh hrel
  exact hh.trans hrel.symm

end ContinuousFlexibility.Radial
