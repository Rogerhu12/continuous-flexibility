module

public import ContinuousFlexibility.Radial.MatchedInnerCompactSupport
public import ContinuousFlexibility.Radial.MatchingInverseFormula
public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Canonical spatial bounds for an actual compact inner region

Only finitely many actual localizers can meet the compact interval
between the cuts. Their labels may be assigned by any fixed map.
The scalar channel is included separately. The norms of the existing
inner inverse and its two existing columns then give a spatial envelope
with no positive radialQ loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real ContinuousFlexibility.Statements
open scoped BigOperators

/-- Compact local finiteness works for any channel labeling. The bound
uses localizer nonvanishing; no equality of constructed cell sets is used. -/
theorem exists_compact_channel_action_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (level : ℕ → ℕ) {K : Set ℝ}
    (hK : IsCompact K) (hcore : K ⊆ radialCore D) :
    ∃ T : ℝ, 0 ≤ T ∧ radialS (level 0) ≤ T ∧
      ∀ m r, r ∈ K → D.localizer m r ≠ 0 → radialS (level (m + 1)) ≤ T := by
  obtain ⟨C, hC⟩ := hD
  have hfinite : Set.Finite {m | (D.cells m ∩ K).Nonempty} :=
    hC.2.2.2.2.2.1 K hK hcore
  obtain ⟨T, hT⟩ :=
    (hfinite.image (fun m => radialS (level (m + 1)))).bddAbove
  refine ⟨max T (radialS (level 0)),
    (radialS_nonneg _).trans (le_max_right _ _), le_max_right _ _, ?_⟩
  intro m r hr hlocal
  have hcell : r ∈ D.cells m := hC.2.1.2.2.1 m hlocal
  exact (hT ⟨m, ⟨r, hcell, hr⟩, rfl⟩).trans (le_max_left _ _)

private theorem matchedCompact_absorb_decay {z B L d : ℝ}
    (hB : 0 ≤ B) (hz : z ≤ B) (hd : d ≤ L) :
    z ≤ (B * exp L) * exp (-d) := by
  have he : 1 ≤ exp (L - d) := one_le_exp_iff.mpr (sub_nonneg.mpr hd)
  calc
    z ≤ B := hz
    _ = B * 1 := (mul_one _).symm
    _ ≤ B * exp (L - d) := mul_le_mul_of_nonneg_left he hB
    _ = _ := by rw [sub_eq_add_neg, exp_add, mul_assoc]

/-- The original restricted inverse and its two original inner columns
have a common envelope. The scalar gate can be either value. -/
theorem matchedInner_compact_spatial_envelope {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (hcore : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (level : ℕ → ℕ) (base : ℕ) (active : Bool) :
    ∃ C : ℝ, 0 < C ∧
      (∀ k m : ℕ,
        ‖matchedModeChannel D hP k ∘L M.innerInverse ∘L
          matchingSourceInnerCLM D M hM ∘L matchedModeScalarGate D active ∘L
            matchedModeChannel D hP m‖ ≤
          C * exp (-|radialS (level k) - radialS (level m)|)) ∧
      ∀ k : ℕ, ∀ i : Fin 2,
        ‖matchedModeChannel D hP k (M.innerPoisson i)‖ ≤
          C * exp (-|radialS (level k) - radialS base|) := by
  classical
  obtain ⟨T, hT, hzero, hlocal⟩ :=
    exists_compact_channel_action_bound hD level isCompact_Icc hcore
  let A : RadialModePair D →L[ℝ] RadialModePair D :=
    M.innerInverse ∘L matchingSourceInnerCLM D M hM ∘L matchedModeScalarGate D active
  let B : ℝ := ‖A‖ + (∑ i : Fin 2, ‖M.innerPoisson i‖) + 1
  have hsum : 0 ≤ ∑ i : Fin 2, ‖M.innerPoisson i‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBA : ‖A‖ ≤ B := by dsimp only [B]; linarith only [hsum]
  have hBP (i : Fin 2) : ‖M.innerPoisson i‖ ≤ B := by
    have hi : ‖M.innerPoisson i‖ ≤ ∑ t : Fin 2, ‖M.innerPoisson t‖ :=
      Finset.single_le_sum (fun t _ => norm_nonneg (M.innerPoisson t)) (Finset.mem_univ i)
    dsimp only [B]
    linarith only [hi, norm_nonneg A]
  let C : ℝ := B * exp (2 * T + radialS base)
  have hC : 0 < C := mul_pos hB (exp_pos _)
  have hvanish (m : ℕ) (hm : T < radialS (level (m + 1))) :
      ∀ r ∈ Icc M.innerLeft M.innerRight, D.localizer m r = 0 := by
    intro r hr
    by_contra hn
    exact not_lt_of_ge (hlocal m r hr hn) hm
  refine ⟨C, hC, ?_, ?_⟩
  · intro k m
    have hbound : ‖matchedModeChannel D hP k ∘L A ∘L matchedModeChannel D hP m‖ ≤ B :=
      (matchedCompact_channel_block_norm_le D hP A k m).trans hBA
    have hgoal :
        ‖matchedModeChannel D hP k ∘L A ∘L matchedModeChannel D hP m‖ ≤
          C * exp (-|radialS (level k) - radialS (level m)|) := by
      by_cases hk : radialS (level k) ≤ T
      · by_cases hm : radialS (level m) ≤ T
        · apply matchedCompact_absorb_decay hB.le hbound
          rw [abs_le]
          constructor <;>
            linarith only [hk, hm, hT, radialS_nonneg (level k),
              radialS_nonneg (level m), radialS_nonneg base]
        · cases m with
          | zero => exact (hm hzero).elim
          | succ m =>
              have hmap : matchedModeChannel D hP k ∘L A ∘L
                  matchedModeChannel D hP (m + 1) = 0 := by
                apply ContinuousLinearMap.ext
                intro F
                simp only [A, ContinuousLinearMap.comp_apply, matchingSourceInnerCLM_apply,
                  matchedModeChannel]
                rw [matchedInnerSource_cell_eq_zero hP M hM active m
                  (hvanish m (lt_of_not_ge hm)) F, map_zero, map_zero,
                  ContinuousLinearMap.zero_apply]
              rw [hmap, norm_zero]
              exact mul_nonneg hC.le (exp_pos _).le
      · cases k with
        | zero => exact (hk hzero).elim
        | succ k =>
            have hmap : matchedModeChannel D hP (k + 1) ∘L A ∘L
                matchedModeChannel D hP m = 0 := by
              apply ContinuousLinearMap.ext
              intro F
              simp only [A, ContinuousLinearMap.comp_apply, matchingSourceInnerCLM_apply,
                matchedModeChannel]
              exact matchedModeCell_eq_zero_of_compact_support hP k _
                (hvanish k (lt_of_not_ge hk))
                (matchedInnerInverse_field_supported hD M hM _)
            rw [hmap, norm_zero]
            exact mul_nonneg hC.le (exp_pos _).le
    simpa only [A, ContinuousLinearMap.comp_assoc] using hgoal
  · intro k i
    have hbound : ‖matchedModeChannel D hP k (M.innerPoisson i)‖ ≤ B :=
      (matchedCompact_channel_norm_apply_le D hP k _).trans (hBP i)
    by_cases hk : radialS (level k) ≤ T
    · apply matchedCompact_absorb_decay hB.le hbound
      rw [abs_le]
      constructor <;>
        linarith only [hk, hT, radialS_nonneg (level k), radialS_nonneg base]
    · cases k with
      | zero => exact (hk hzero).elim
      | succ k =>
          have hz : matchedModeChannel D hP (k + 1) (M.innerPoisson i) = 0 :=
            matchedModeCell_eq_zero_of_compact_support hP k _
              (hvanish k (lt_of_not_ge hk)) (matchedInnerPoisson_field_supported hD M hM i)
          rw [hz, norm_zero]
          exact mul_nonneg hC.le (exp_pos _).le

end ContinuousFlexibility.Radial
