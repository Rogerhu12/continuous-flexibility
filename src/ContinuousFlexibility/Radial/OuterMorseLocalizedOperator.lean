module

public import ContinuousFlexibility.Radial.OuterActualGreenData
public import ContinuousFlexibility.Radial.OuterLocalizedOperator
public import ContinuousFlexibility.Radial.OuterMorsePointLabels
public import ContinuousFlexibility.Radial.OuterWholeLocalizerDensity

/-!
# Localizing the same actual Morse outer inverse

Position labels of the actual core and deep edges are converted to the
physical labels of the specified localizers. The same kernel then bounds
the two actual multiplier compositions with the constructed Robin inverse.
Every exponent below is fixed by the point exponent, common coefficient
bounds and common endpoints, before the profile or frequency is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements

/-- Every real coefficient power is nonnegative; the action factor is the
only additional sign condition in the localized envelope. -/
theorem outerMorse_localized_envelope_nonneg (i k : ℕ) (A : ℝ)
    {action : ℝ} (hact : 0 ≤ action) :
    0 ≤ radialE i ^ A * radialE k ^ A * action *
      exp (-|radialS i - radialS k|) :=
  mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (rpow_nonneg (show 0 ≤ radialE i from (exp_pos _).le) _)
        (rpow_nonneg (show 0 ≤ radialE k from (exp_pos _).le) _)) hact)
    (exp_pos _).le

def outerMorseShiftExponent (A : ℝ) (hA : 0 ≤ A) : ℝ :=
  Classical.choose (outer_localized_envelope_shift hA)

theorem outerMorseShiftExponent_pos (A : ℝ) (hA : 0 ≤ A) :
    0 < outerMorseShiftExponent A hA :=
  (Classical.choose_spec (outer_localized_envelope_shift hA)).1

theorem outerMorseShiftExponent_bound (A : ℝ) (hA : 0 ≤ A)
    {p q i k : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hi : 1 ≤ i) (hk : 1 ≤ k)
    (hpi : p ≤ i + 2) (hip : i ≤ p + 2) (hqk : q ≤ k + 2) (hkq : k ≤ q + 2) :
    radialE p ^ A * radialE q ^ A * exp (-|radialS p - radialS q|) ≤
      radialE i ^ outerMorseShiftExponent A hA * radialE k ^ outerMorseShiftExponent A hA *
        exp (-|radialS i - radialS k|) :=
  (Classical.choose_spec (outer_localized_envelope_shift hA)).2 p q i k
    hp hq hi hk hpi hip hqk hkq

def outerMorseWholeMassBound (a b : ℝ) (C : ℕ → ℝ) : ℝ :=
  12 * C 0 * exp ((C 0) ^ 5) * (b - a) / a ^ 2

theorem outerMorseWholeMassBound_nonneg {a b : ℝ} {C : ℕ → ℝ}
    (hC : 0 < C 0) (ha : 0 < a) (hab : a < b) :
    0 ≤ outerMorseWholeMassBound a b C := by
  have hba : 0 < b - a := sub_pos.mpr hab
  unfold outerMorseWholeMassBound
  positivity

def outerMorseOperatorExponent (a b : ℝ) (C : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A) : ℝ :=
  outerMorseWholeMassBound a b C + outerMorseShiftExponent A hA + outerMorseShiftExponent A hA

theorem outerMorseOperatorExponent_pos {a b : ℝ} {C : ℕ → ℝ}
    (hC : 0 < C 0) (ha : 0 < a) (hab : a < b) (A : ℝ) (hA : 0 ≤ A) :
    0 < outerMorseOperatorExponent a b C A hA := by
  have hm := outerMorseWholeMassBound_nonneg hC ha hab
  have hs := outerMorseShiftExponent_pos A hA
  unfold outerMorseOperatorExponent
  linarith only [hm, hs]

/-- A zero physical label has no support on the chosen whole outer interval. -/
theorem morseOuter_localizer_zero_on_whole
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) {entry η K : ℝ} {right : Bool} {j N m : ℕ}
    (hN : M.index + 3 ≤ N) (hlabels : MorseOuterLocalizerLabels M D N)
    (hm : D.cellIndex m = 0) {x : ℝ}
    (hx : x ∈ Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    D.localizer m (outerOutwardRadius right x) = 0 := by
  by_contra hz
  have hx' : x ∈ Ico (morseTransitionOutwardLeft M entry right N)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) := by
    rw [morseTransitionOutwardLeft_eq]
    exact ⟨hx.1.le, hx.2⟩
  obtain ⟨p, hp⟩ := exists_morseOuterPoint h right j N (by omega) entry η K hx'
  have hi := morseOuterPoint_localizer_pos hN hlabels hp hz
  omega

/-- A bound on the actual position kernel bounds the specified localized
kernel, retaining the complete cubic attenuation between physical labels. -/
theorem morseOuter_localized_point_kernel_bound
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) {entry η K A action : ℝ}
    {right : Bool} {j N : ℕ} (hN : M.index + 3 ≤ N)
    (hlabels : MorseOuterLocalizerLabels M D N) (hA : 0 ≤ A) (hact : 0 ≤ action)
    {kernel : ℝ → ℝ → ℝ}
    (hpoint : ∀ p q x y, MorseOuterPoint M D entry right j N η K p x →
      MorseOuterPoint M D entry right j N η K q y →
      |kernel x y| ≤ radialE p ^ A * radialE q ^ A * action * exp (-|radialS p - radialS q|))
    (k m : ℕ) {x y : ℝ}
    (hx : x ∈ Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hy : y ∈ Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    |outerWholeLocalizedKernel D right k m kernel x y| ≤
      radialE (D.cellIndex k) ^ outerMorseShiftExponent A hA *
        radialE (D.cellIndex m) ^ outerMorseShiftExponent A hA * action *
          exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|) := by
  have htarget : 0 ≤ radialE (D.cellIndex k) ^ outerMorseShiftExponent A hA *
      radialE (D.cellIndex m) ^ outerMorseShiftExponent A hA * action *
        exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|) :=
    outerMorse_localized_envelope_nonneg _ _ _ hact
  by_cases hk0 : D.localizer k (outerOutwardRadius right x) = 0
  · simpa only [outerWholeLocalizedKernel, hk0, zero_mul, abs_zero] using htarget
  by_cases hm0 : D.localizer m (outerOutwardRadius right y) = 0
  · simpa only [outerWholeLocalizedKernel, hm0, mul_zero, abs_zero] using htarget
  have hx' : x ∈ Ico (morseTransitionOutwardLeft M entry right N)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) := by
    rw [morseTransitionOutwardLeft_eq]
    exact ⟨hx.1.le, hx.2⟩
  have hy' : y ∈ Ico (morseTransitionOutwardLeft M entry right N)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) := by
    rw [morseTransitionOutwardLeft_eq]
    exact ⟨hy.1.le, hy.2⟩
  obtain ⟨p, hp⟩ := exists_morseOuterPoint h right j N (by omega) entry η K hx'
  obtain ⟨q, hq⟩ := exists_morseOuterPoint h right j N (by omega) entry η K hy'
  have hpN := morseOuterPoint_label_ge hp
  have hqN := morseOuterPoint_label_ge hq
  have hk := morseOuterPoint_localizer_pos hN hlabels hp hk0
  have hm := morseOuterPoint_localizer_pos hN hlabels hq hm0
  have hki := morseOuterPoint_localizer_labels (by omega : M.index < N) hlabels hp hk0
  have hmi := morseOuterPoint_localizer_labels (by omega : M.index < N) hlabels hq hm0
  have hshift := outerMorseShiftExponent_bound A hA (by omega : 1 ≤ p) (by omega : 1 ≤ q)
    hk hm hki.1 hki.2 hmi.1 hmi.2
  have hraw : |kernel x y| ≤ radialE (D.cellIndex k) ^ outerMorseShiftExponent A hA *
      radialE (D.cellIndex m) ^ outerMorseShiftExponent A hA * action *
        exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|) := by
    calc
      _ ≤ (radialE p ^ A * radialE q ^ A * exp (-|radialS p - radialS q|)) * action :=
        (hpoint p q x y hp hq).trans_eq (by ring)
      _ ≤ (radialE (D.cellIndex k) ^ outerMorseShiftExponent A hA *
          radialE (D.cellIndex m) ^ outerMorseShiftExponent A hA *
          exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) * action :=
        mul_le_mul_of_nonneg_right hshift hact
      _ = _ := by ring
  have hpart : RadialPartition D := h.accumulating.2.1
  have hcut : |D.localizer k (outerOutwardRadius right x)| *
      |D.localizer m (outerOutwardRadius right y)| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul
      (outer_partition_localizer_abs_le_one hpart k (outerOutwardRadius right x))
      (outer_partition_localizer_abs_le_one hpart m (outerOutwardRadius right y))
      (abs_nonneg _) zero_le_one
  calc
    _ = (|D.localizer k (outerOutwardRadius right x)| *
        |D.localizer m (outerOutwardRadius right y)|) * |kernel x y| := by
      simp only [outerWholeLocalizedKernel, abs_mul]
      ring
    _ ≤ 1 * |kernel x y| := mul_le_mul_of_nonneg_right hcut (abs_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hraw

/-- This is the norm of the actual two-multiplier composition with the
same constructed Robin inverse, for every pair of localizers. -/
theorem MorseOuterGreenData.localized_norm_le
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {right : Bool} {j N : ℕ} {entry η K lam Cbound Co a b A action : ℝ}
    (F : MorseOuterGreenData M D right N j entry η K lam Cbound Co)
    (h : MorseChainRealization M σ D C) (ha : D.a = a) (hb : D.b = b)
    (he : entry ∈ morseInitialMiddle M) (hN : M.index + 3 ≤ N)
    (hlabels : MorseOuterLocalizerLabels M D N) (hA : 0 ≤ A) (hact : 0 ≤ action)
    (hpoint : ∀ p q x y, MorseOuterPoint M D entry right j N η K p x →
      MorseOuterPoint M D entry right j N η K q y →
      |outerGreenKernel lam F.pair.U F.pair.V x y| ≤
        radialE p ^ A * radialE q ^ A * action * exp (-|radialS p - radialS q|))
    (k m : ℕ) :
    ‖outerWholeLocalizedOperator h.accumulating.2.1 right
        (morseTransitionPhysicalEntry M entry right N) k m F.inverse.operator‖ ≤
      radialE (D.cellIndex k) ^ outerMorseOperatorExponent a b C A hA *
        radialE (D.cellIndex m) ^ outerMorseOperatorExponent a b C A hA * action *
          exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|) := by
  have hD : IsAccumulatingProfile D := ⟨C, h.accumulating⟩
  have hentry := morseTransitionPhysicalEntry_mem_core h he right N (by omega)
  have hrow := outerGreenKernel_rows_aestronglyMeasurable (lam := lam)
    (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right N))
    (outerWholeMeasure_ae_mem hentry) F.pair.U_system.continuousOn.1 F.pair.V_system.continuousOn.1
  have hmass : (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right N)).real univ ≤
      outerMorseWholeMassBound a b C := by
    simpa only [outerMorseWholeMassBound, ha, hb] using
      outerWholeMeasure_mass_bound h.accumulating right (morseTransitionPhysicalEntry M entry right N)
  have hmass0 : 0 ≤ outerMorseWholeMassBound a b C :=
    (show 0 ≤ (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right N)).real univ
      from by rw [measureReal_def]; exact ENNReal.toReal_nonneg).trans hmass
  have hS : 0 ≤ outerMorseShiftExponent A hA := (outerMorseShiftExponent_pos A hA).le
  have hzero (hz : D.cellIndex k = 0 ∨ D.cellIndex m = 0) :
      ‖outerWholeLocalizedOperator h.accumulating.2.1 right
        (morseTransitionPhysicalEntry M entry right N) k m F.inverse.operator‖ ≤ 0 := by
    have hh := outerWholeLocalizedOperator_norm_le hD h.accumulating.2.1 right hentry k m
      F.inverse.operator (outerGreenKernel lam F.pair.U F.pair.V) F.inverse.kernel hrow
      (B := 0) (by norm_num) (by
        intro x hx y hy
        rcases hz with hk | hm
        · rw [morseOuter_localizer_zero_on_whole (j := j) (η := η) (K := K)
            h hN hlabels hk hx, zero_mul, zero_mul, abs_zero]
        · rw [morseOuter_localizer_zero_on_whole (j := j) (η := η) (K := K)
            h hN hlabels hm hy, mul_zero, abs_zero])
    simpa only [mul_zero] using hh
  by_cases hk : 1 ≤ D.cellIndex k
  · by_cases hm : 1 ≤ D.cellIndex m
    · have hB : 0 ≤ radialE (D.cellIndex k) ^ outerMorseShiftExponent A hA *
          radialE (D.cellIndex m) ^ outerMorseShiftExponent A hA * action *
            exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|) :=
        outerMorse_localized_envelope_nonneg _ _ _ hact
      have hh := outerWholeLocalizedOperator_norm_le hD h.accumulating.2.1 right hentry k m
        F.inverse.operator (outerGreenKernel lam F.pair.U F.pair.V) F.inverse.kernel hrow hB
        (fun x hx y hy => morseOuter_localized_point_kernel_bound h hN hlabels hA hact hpoint k m hx hy)
      have hcoeff := outer_envelope_pair_prefactor (n := D.cellIndex m) hk hmass0 hS hS
      calc
        _ ≤ (outerWholeMeasure D right (morseTransitionPhysicalEntry M entry right N)).real univ *
            (radialE (D.cellIndex k) ^ outerMorseShiftExponent A hA *
              radialE (D.cellIndex m) ^ outerMorseShiftExponent A hA * action *
                exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) := hh
        _ ≤ outerMorseWholeMassBound a b C *
            (radialE (D.cellIndex k) ^ outerMorseShiftExponent A hA *
              radialE (D.cellIndex m) ^ outerMorseShiftExponent A hA * action *
                exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) :=
          mul_le_mul_of_nonneg_right hmass hB
        _ = (outerMorseWholeMassBound a b C * radialE (D.cellIndex k) ^ outerMorseShiftExponent A hA *
            radialE (D.cellIndex m) ^ outerMorseShiftExponent A hA) *
              (action * exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) := by ring
        _ ≤ (radialE (D.cellIndex k) ^ outerMorseOperatorExponent a b C A hA *
            radialE (D.cellIndex m) ^ outerMorseOperatorExponent a b C A hA) *
              (action * exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) :=
          mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hact (exp_pos _).le)
        _ = _ := by ring
    · exact (hzero (Or.inr (by omega))).trans
        (outerMorse_localized_envelope_nonneg _ _ _ hact)
  · exact (hzero (Or.inl (by omega))).trans
      (outerMorse_localized_envelope_nonneg _ _ _ hact)

end ContinuousFlexibility.Radial
