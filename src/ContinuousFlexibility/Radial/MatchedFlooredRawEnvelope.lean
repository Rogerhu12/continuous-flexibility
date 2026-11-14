module

public import ContinuousFlexibility.Radial.ReferenceRawKernelSchur
public import ContinuousFlexibility.Radial.MatchedWeightFlooredMorseFibers

/-!
# Raw channel envelopes on the actual return-margin reference

The index floor contracts the action distance between two field cells.
The scalar channel remains at level zero, so a field-to-border or
border-to-field comparison pays at most exp(S N). This fixed cost is
retained explicitly. Neither the kernel nor any physical operator is
changed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem radialS_index_floor_le (m N : ℕ) :
    radialS (max m N) ≤ radialS m + radialS N := by
  rcases le_total m N with h | h
  · rw [max_eq_right h]
    linarith only [radialS_nonneg m]
  · rw [max_eq_left h]
    linarith only [radialS_nonneg N]

theorem radialS_index_floor_gap_le (k m N : ℕ) :
    |radialS (max k N) - radialS (max m N)| ≤ |radialS k - radialS m| := by
  have hordered (a b : ℕ) (hab : a ≤ b) :
      radialS (max b N) - radialS (max a N) ≤ radialS b - radialS a := by
    rcases le_total N a with hNa | haN
    · rw [max_eq_left hNa, max_eq_left (hNa.trans hab)]
    · rw [max_eq_right haN]
      rcases le_total N b with hNb | hbN
      · rw [max_eq_left hNb]
        linarith only [radialS_monotone haN]
      · rw [max_eq_right hbN]
        linarith only [radialS_monotone hab]
  rcases le_total k m with hkm | hmk
  · rw [abs_of_nonpos (sub_nonpos.mpr
      (radialS_monotone (max_le_max hkm le_rfl))),
      abs_of_nonpos (sub_nonpos.mpr (radialS_monotone hkm))]
    linarith only [hordered k m hkm]
  · rw [abs_of_nonneg (sub_nonneg.mpr
      (radialS_monotone (max_le_max hmk le_rfl))),
      abs_of_nonneg (sub_nonneg.mpr (radialS_monotone hmk))]
    exact hordered m k hmk

theorem referenceRawChannelLevel_floor_Q {D E : ReferenceData} {N : ℕ}
    (hindex : E.cellIndex = fun m => max (D.cellIndex m) N) (k : ℕ) :
    radialQ (referenceRawChannelLevel D k) ≤ radialQ (referenceRawChannelLevel E k) := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
      change radialQ (D.cellIndex k) ≤ radialQ (E.cellIndex k)
      rw [hindex]
      exact radialQ_monotone (le_max_left _ _)

theorem referenceRawChannelLevel_floor_S_gap {D E : ReferenceData} {N : ℕ}
    (hindex : E.cellIndex = fun m => max (D.cellIndex m) N) (k m : ℕ) :
    |radialS (referenceRawChannelLevel E k) - radialS (referenceRawChannelLevel E m)| ≤
      |radialS (referenceRawChannelLevel D k) - radialS (referenceRawChannelLevel D m)| +
        radialS N := by
  cases k with
  | zero =>
      cases m with
      | zero => simpa only [sub_self, abs_zero, zero_add] using radialS_nonneg N
      | succ m =>
          change |radialS 0 - radialS (E.cellIndex m)| ≤
            |radialS 0 - radialS (D.cellIndex m)| + radialS N
          rw [hindex]
          simp only [radialS_zero, zero_sub, abs_neg,
            abs_of_nonneg (radialS_nonneg _)]
          exact radialS_index_floor_le (D.cellIndex m) N
  | succ k =>
      cases m with
      | zero =>
          change |radialS (E.cellIndex k) - radialS 0| ≤
            |radialS (D.cellIndex k) - radialS 0| + radialS N
          rw [hindex]
          simp only [radialS_zero, sub_zero, abs_of_nonneg (radialS_nonneg _)]
          exact radialS_index_floor_le (D.cellIndex k) N
      | succ m =>
          change |radialS (E.cellIndex k) - radialS (E.cellIndex m)| ≤
            |radialS (D.cellIndex k) - radialS (D.cellIndex m)| + radialS N
          rw [hindex]
          exact (radialS_index_floor_gap_le (D.cellIndex k) (D.cellIndex m) N).trans
            (le_add_of_nonneg_right (radialS_nonneg N))

theorem referenceRawChannel_envelope_floor {D E : ReferenceData} {N : ℕ}
    (hindex : E.cellIndex = fun m => max (D.cellIndex m) N)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (k m : ℕ) :
    C * exp (a * (radialQ (referenceRawChannelLevel D k) +
      radialQ (referenceRawChannelLevel D m)) -
      |radialS (referenceRawChannelLevel D k) - radialS (referenceRawChannelLevel D m)|) ≤
    (C * exp (radialS N)) * exp (a * (radialQ (referenceRawChannelLevel E k) +
      radialQ (referenceRawChannelLevel E m)) -
      |radialS (referenceRawChannelLevel E k) - radialS (referenceRawChannelLevel E m)|) := by
  have hQ := mul_le_mul_of_nonneg_left
    (add_le_add (referenceRawChannelLevel_floor_Q hindex k)
      (referenceRawChannelLevel_floor_Q hindex m)) ha
  have hS := referenceRawChannelLevel_floor_S_gap hindex k m
  calc
    _ ≤ C * exp (radialS N +
        (a * (radialQ (referenceRawChannelLevel E k) + radialQ (referenceRawChannelLevel E m)) -
          |radialS (referenceRawChannelLevel E k) - radialS (referenceRawChannelLevel E m)|)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hQ, hS])) hC
    _ = _ := by rw [exp_add]; ring

theorem referenceRawChannelLevel_floored_morse_fiber_bound
    {D : ReferenceData} {base N : ℕ}
    (hindex : D.cellIndex = fun m =>
      max (morseTwoTailAt base (fun _ k => base + k) m) N) (n : ℕ) :
    Set.Finite {k | referenceRawChannelLevel D k = n} ∧
      Set.ncard {k | referenceRawChannelLevel D k = n} ≤ 2 * N + 4 := by
  have hcell (n : ℕ) : Set.Finite {m | D.cellIndex m = n} ∧
      Set.ncard {m | D.cellIndex m = n} ≤ 2 * N + 3 := by
    simpa only [hindex] using morseTwoTailAt_floor_level_fiber_bound base N n
  obtain ⟨hf, hc⟩ := referenceRawChannelLevel_fiber_bound D (2 * N + 3)
    (fun n => (hcell n).1) (fun n => (hcell n).2) n
  refine ⟨hf, ?_⟩
  omega

end ContinuousFlexibility.Radial
