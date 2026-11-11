import ContinuousFlexibility.Radial.OuterDeepUniformProduct
import ContinuousFlexibility.Radial.OuterLocalizerCutoff
import ContinuousFlexibility.Radial.OuterPhysicalTailBasis
import ContinuousFlexibility.Radial.OuterWholeMeasure

/-!
# A true deep cutoff for every fixed outer frequency and regular cut

The cutoff moves beyond the supplied regular cut and beyond all proved
uniform deep-tail thresholds. Small transition indices are therefore
handled by the same physical basis, with a larger compact core.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology
open ContinuousFlexibility.Statements

theorem morseRealized_deepEntrance_tendsto
    {M : MorseChainData} {σ C : ℕ → ℝ} {D : ReferenceData}
    (h : MorseChainRealization M σ D C) (right : Bool) :
    Tendsto (morseOuterDeepEntrance M right) atTop
      (𝓝 (tailPhysicalEndpoint D right)) := by
  have hlim : ∀ side : Bool,
      Tendsto (fun n => M.radius side n (M.leftX side n)) atTop
        (𝓝 (if side then D.b else D.a)) := by
    rcases h with ⟨_, _, _, _, _, _, hh, _, _, _⟩
    exact fun side => (hh side).1
  cases right with
  | false =>
      change Tendsto (fun n => M.radius false n (M.leftX false n)) atTop (𝓝 D.a)
      exact hlim false
  | true =>
      have hl := (hlim true).comp (tendsto_add_atTop_nat 1)
      apply hl.congr'
      filter_upwards [eventually_ge_atTop M.index] with n hn
      simpa only [morseOuterDeepEntrance, ite_true, Function.comp_apply]
        using (h.join_data true n hn).2.2.1.symm

theorem morseRealized_eventually_deep_after_cut
    {M : MorseChainData} {σ C : ℕ → ℝ} {D : ReferenceData}
    (h : MorseChainRealization M σ D C) (right : Bool) {cut : ℝ}
    (hcut : cut ∈ radialCore D) :
    ∀ᶠ n : ℕ in atTop, outerOutwardRadius right cut <
      outerOutwardRadius right (morseOuterDeepEntrance M right n) := by
  have hc : Continuous (outerOutwardRadius right) := by
    cases right
    · exact continuous_id.neg
    · exact continuous_id
  have ht := hc.continuousAt.tendsto.comp (morseRealized_deepEntrance_tendsto h right)
  exact ht.eventually (Ioi_mem_nhds (outerWhole_interval (right := right) hcut))

theorem exists_matchedMorse_fixed_deep_cutoff
    {M : MorseChainData} {C : ℕ → ℝ}
    {family : (ℕ → ℝ) → ReferenceData} {Cstar η K : ℝ}
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    (hCstar : 0 < Cstar) (hη0 : 0 < η) (hη : η ≤ 1 / 16)
    (hK : 32 ≤ K) (minimum : ℕ)
    (σ : ℕ → ℝ) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (right : Bool) (j : ℕ) (hj : 2 ≤ j) {cut : ℝ}
    (hcut : cut ∈ radialCore (family σ)) :
    ∃ Ad : ℝ, 0 < Ad ∧ ∃ N : ℕ, minimum ≤ N ∧ M.index + 3 ≤ N ∧
      (j : ℝ) < radialFrequencyThreshold M Cstar N ∧
      outerOutwardRadius right cut <
        outerOutwardRadius right (morseOuterDeepEntrance M right N) ∧
      MorseOuterLocalizerLabels M (family σ) N ∧
      let T := morsePhysicalDeepTail M (family σ) right j (N + 1)
        (morseOuterDeepEntrance M right N) η K
      DeepTailHypotheses T ∧ TailPhysicalRelation (family σ) T right j (N + 1) ∧
      T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ ∧
      (∀ k : ℕ, exp (2 * ((N + 1 + k : ℕ) : ℝ) ^ 2 -
        Ad * (((N + 1 + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (N + 1 + k : ℕ))) ≤
          T.Λ * tailMass T (k + 1) * tailResistance T k) ∧
      Nonempty (MorsePhysicalTailBasis M (family σ) right j (N + 1)
        (morseOuterDeepEntrance M right N) η K) := by
  have h := (hfamily σ hσ).1
  obtain ⟨Ad, hAd, Np, hmin, hidx, h31, hdata⟩ :=
    outer_exists_uniform_actual_deepTailProduct M C family hfamily hends hCstar hη0
      (by linarith only [hη]) (by linarith only [hK])
      (max minimum (M.index + 3))
  obtain ⟨Nl, hlabels⟩ := eventually_atTop.mp
    (morseOuter_eventually_uniform_localizer_labels M C family
      (fun σ hσ => (hfamily σ hσ).1) hends)
  have hupper := (morseTransition_threshold_tendsto M hCstar h.d_eq).eventually
    (eventually_gt_atTop (j : ℝ))
  obtain ⟨N, hN, hjN, hcutN⟩ :=
    ((eventually_ge_atTop (max Np Nl)).and
      (hupper.and (morseRealized_eventually_deep_after_cut h right hcut))).exists
  have hNp : Np ≤ N := (le_max_left _ _).trans hN
  have hNl : Nl ≤ N := (le_max_right _ _).trans hN
  have hlarge : M.index + 3 ≤ N := (le_max_right _ _).trans (hmin.trans hNp)
  have hd := hdata N hNp σ hσ j hj hjN right
  refine ⟨Ad, hAd, N, (le_max_left _ _).trans (hmin.trans hNp), hlarge,
    hjN, hcutN, (hlabels N hNl).2 σ hσ, hd.2.1, hd.2.2.1, hd.1, hd.2.2.2, ?_⟩
  exact exists_morsePhysicalTailBasis h.geometry right j (N + 1)
    (h.geometry.1.trans (morseOuterDeepEntrance_mem_core h right N (by omega)).1)
    hd.2.1 hη hK

end ContinuousFlexibility.Radial
