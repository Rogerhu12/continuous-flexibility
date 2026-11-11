import ContinuousFlexibility.Radial.ReferenceRawKernelSchur
import ContinuousFlexibility.Radial.MatchedPhysicalChannelComparison
import ContinuousFlexibility.Radial.InnerWeightL2

/-!
# Actual cell blocks from the two physical weight signs

The field weights are genuine multiplication on the original radial L²
space and leave the one border scalar unchanged. Two bounded weighted
realizations of the same operator imply exponential off-diagonal decay
of its actual localizer blocks. Output and input weights may differ:
this retains the fixed output coefficient loss in the inner inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ENNReal

/-- Actual multiplication of the field, with the original scalar fixed. -/
def matchedModeActualWeight (D : ReferenceData)
    (W : ℝ → ℝ) (hW : Measurable W) (hpos : ∀ r, 0 < W r)
    (CW CV : ℝ) (hCW : ∀ r, |W r| ≤ CW) (hCV : ∀ r, |(W r)⁻¹| ≤ CV) :
    RadialModePair D ≃L[ℝ] RadialModePair D :=
  (innerWeightEquiv (radialHilbertMeasure D) W hW hpos CW CV hCW hCV).prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)

theorem matchedMode_fieldWeight_commutes (D : ReferenceData)
    (hP : RadialPartition D) (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D)
    (w : ℝ → ℝ)
    (hE : ∀ u, E u =ᵐ[radialHilbertMeasure D] fun r => w r * u r) (k : ℕ) :
    (E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) :
      RadialModePair D →L[ℝ] RadialModePair D) ∘L matchedModeChannel D hP k =
    matchedModeChannel D hP k ∘L
      (E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) :
        RadialModePair D →L[ℝ] RadialModePair D) := by
  apply ContinuousLinearMap.ext
  intro U
  cases k with
  | zero =>
    change (E 0, U.2) = (0, U.2)
    rw [map_zero]
  | succ m =>
    change (E (matchedModeCellL2 D hP m U.1), 0) =
      (matchedModeCellL2 D hP m (E U.1), 0)
    congr 1
    apply Lp.ext
    filter_upwards [hE (matchedModeCellL2 D hP m U.1),
      matchedModeCellL2_ae D hP m U.1, matchedModeCellL2_ae D hP m (E U.1),
      hE U.1] with r he hc hce heu
    rw [he, hc, hce, heu]
    ring

theorem norm_matchedMode_fieldWeight_channel_le (D : ReferenceData)
    (hP : RadialPartition D) (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D)
    (w : ℝ → ℝ)
    (hE : ∀ u, E u =ᵐ[radialHilbertMeasure D] fun r => w r * u r)
    (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) (hA₀ : 1 ≤ A 0)
    (hcell : ∀ m r, r ∈ D.cells m → |w r| ≤ A (m + 1)) (k : ℕ) :
    ‖(E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) :
      RadialModePair D →L[ℝ] RadialModePair D) ∘L matchedModeChannel D hP k‖ ≤ A k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (hA k)
  intro U
  cases k with
  | zero =>
    change ‖(E 0, U.2)‖ ≤ A 0 * ‖U‖
    rw [map_zero, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg U.2)]
    calc
      ‖U.2‖ ≤ ‖U‖ := le_max_right _ _
      _ = 1 * ‖U‖ := (one_mul _).symm
      _ ≤ A 0 * ‖U‖ := mul_le_mul_of_nonneg_right hA₀ (norm_nonneg U)
  | succ m =>
    change ‖(E (matchedModeCellL2 D hP m U.1), (0 : ℝ))‖ ≤ A (m + 1) * ‖U‖
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
    have hpoint : ∀ r, |w r * D.localizer m r| ≤ A (m + 1) := by
      intro r
      by_cases hz : D.localizer m r = 0
      · simpa only [hz, mul_zero, abs_zero] using hA (m + 1)
      · rw [abs_mul]
        calc
          |w r| * |D.localizer m r| ≤ A (m + 1) * 1 :=
            mul_le_mul (hcell m r (hP.2.2.1 m hz))
              (matchedRadialLocalizer_abs_le_one hP m r) (abs_nonneg _) (hA _)
          _ = _ := mul_one _
    have hfield : ‖E (matchedModeCellL2 D hP m U.1)‖ ≤ A (m + 1) * ‖U.1‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hE (matchedModeCellL2 D hP m U.1),
        matchedModeCellL2_ae D hP m U.1] with r he hc
      rw [he, hc, ← mul_assoc, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hpoint r) (abs_nonneg _)
    exact hfield.trans
      (mul_le_mul_of_nonneg_left (le_max_left ‖U.1‖ ‖U.2‖) (hA _))

private theorem matchedMode_twoWeight_block_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E F : H ≃L[ℝ] H) (Q T R : H →L[ℝ] H)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hQ : ‖Q ∘L (E.symm : H →L[ℝ] H)‖ ≤ a)
    (hT : ‖(E : H →L[ℝ] H) ∘L T ∘L (F.symm : H →L[ℝ] H)‖ ≤ b)
    (hR : ‖(F : H →L[ℝ] H) ∘L R‖ ≤ c) :
    ‖Q ∘L T ∘L R‖ ≤ a * b * c := by
  have hfactor :
      Q ∘L T ∘L R = (Q ∘L (E.symm : H →L[ℝ] H)) ∘L
        (((E : H →L[ℝ] H) ∘L T ∘L (F.symm : H →L[ℝ] H)) ∘L
          ((F : H →L[ℝ] H) ∘L R)) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [hfactor]
  calc
    _ ≤ ‖Q ∘L (E.symm : H →L[ℝ] H)‖ *
        (‖(E : H →L[ℝ] H) ∘L T ∘L (F.symm : H →L[ℝ] H)‖ *
          ‖(F : H →L[ℝ] H) ∘L R‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ a * (b * c) :=
      mul_le_mul hQ
        (mul_le_mul hT hR (norm_nonneg _) hb)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ha
    _ = _ := by ring

/-- Two genuine physical weight signs give the actual augmented cell
kernel. The pointwise hypotheses concern only the weight functions on
cell supports. In particular, they allow an inverse output loss, whose
coefficient power is absorbed in `a`. The scalar channel has level zero
and unchanged weight one. -/
theorem matchedMode_twoSign_cell_envelope
    (D : ReferenceData) (hP : RadialPartition D)
    (T : RadialModePair D →L[ℝ] RadialModePair D)
    (Wo Wi : Bool → ℝ → ℝ)
    (hWo : ∀ s, Measurable (Wo s)) (hWi : ∀ s, Measurable (Wi s))
    (ho : ∀ s r, 0 < Wo s r) (hi : ∀ s r, 0 < Wi s r)
    (Bo Co Bi Ci : Bool → ℝ)
    (hBo : ∀ s r, |Wo s r| ≤ Bo s) (hCo : ∀ s r, |(Wo s r)⁻¹| ≤ Co s)
    (hBi : ∀ s r, |Wi s r| ≤ Bi s) (hCi : ∀ s r, |(Wi s r)⁻¹| ≤ Ci s)
    {C R a : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hweighted : ∀ s : Bool,
      ‖(matchedModeActualWeight D (Wo s) (hWo s) (ho s) (Bo s) (Co s) (hBo s) (hCo s) :
          RadialModePair D →L[ℝ] RadialModePair D) ∘L T ∘L
        ((matchedModeActualWeight D (Wi s) (hWi s) (hi s) (Bi s) (Ci s) (hBi s) (hCi s)).symm :
          RadialModePair D →L[ℝ] RadialModePair D)‖ ≤ C)
    (hlocal : ∀ s m r, r ∈ D.cells m →
      |(Wo s r)⁻¹| ≤ R * Real.exp (a * radialQ (D.cellIndex m) -
        (if s then radialS (D.cellIndex m) else -radialS (D.cellIndex m))) ∧
      |Wi s r| ≤ R * Real.exp (a * radialQ (D.cellIndex m) +
        (if s then radialS (D.cellIndex m) else -radialS (D.cellIndex m))))
    (k m : ℕ) :
    ‖matchedModeChannel D hP k ∘L T ∘L matchedModeChannel D hP m‖ ≤
      C * R ^ 2 * Real.exp
        (a * (radialQ (referenceRawChannelLevel D k) + radialQ (referenceRawChannelLevel D m)) -
          |radialS (referenceRawChannelLevel D k) - radialS (referenceRawChannelLevel D m)|) := by
  let level := referenceRawChannelLevel D
  let height : Bool → ℕ → ℝ := fun s i =>
    if s then radialS (level i) else -radialS (level i)
  let A : Bool → ℕ → ℝ := fun s i => R * Real.exp (a * radialQ (level i) - height s i)
  let B : Bool → ℕ → ℝ := fun s i => R * Real.exp (a * radialQ (level i) + height s i)
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hA : ∀ s i, 0 ≤ A s i := fun s i => mul_nonneg hR₀ (Real.exp_pos _).le
  have hB : ∀ s i, 0 ≤ B s i := fun s i => mul_nonneg hR₀ (Real.exp_pos _).le
  have hq₀ : radialQ 0 = 0 := by norm_num [radialQ]
  have hs₀ : radialS 0 = 0 := by norm_num [radialS]
  have hA₀ : ∀ s, 1 ≤ A s 0 := by
    intro s
    simpa only [A, height, level, referenceRawChannelLevel, hq₀, hs₀,
      neg_zero, ite_self, mul_zero, sub_zero, Real.exp_zero, mul_one] using hR
  have hB₀ : ∀ s, 1 ≤ B s 0 := by
    intro s
    simpa only [B, height, level, referenceRawChannelLevel, hq₀, hs₀,
      neg_zero, ite_self, mul_zero, add_zero, Real.exp_zero, mul_one] using hR
  have hsign (s : Bool) :
      ‖matchedModeChannel D hP k ∘L T ∘L matchedModeChannel D hP m‖ ≤
        C * R ^ 2 * Real.exp
          (a * (radialQ (level k) + radialQ (level m)) - height s k + height s m) := by
    let Eo := innerWeightEquiv (radialHilbertMeasure D)
      (Wo s) (hWo s) (ho s) (Bo s) (Co s) (hBo s) (hCo s)
    let Ei := innerWeightEquiv (radialHilbertMeasure D)
      (Wi s) (hWi s) (hi s) (Bi s) (Ci s) (hBi s) (hCi s)
    have heo : ∀ u, Eo.symm u =ᵐ[radialHilbertMeasure D] fun r => (Wo s r)⁻¹ * u r :=
      innerWeightEquiv_symm_ae (radialHilbertMeasure D) (Wo s) (hWo s) (ho s)
        (Bo s) (Co s) (hBo s) (hCo s)
    have hei : ∀ u, Ei u =ᵐ[radialHilbertMeasure D] fun r => Wi s r * u r :=
      innerWeightEquiv_ae (radialHilbertMeasure D) (Wi s) (hWi s) (hi s)
        (Bi s) (Ci s) (hBi s) (hCi s)
    have hout :
        ‖matchedModeChannel D hP k ∘L
          (Eo.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) :
            RadialModePair D →L[ℝ] RadialModePair D)‖ ≤ A s k := by
      rw [← matchedMode_fieldWeight_commutes D hP Eo.symm (fun r => (Wo s r)⁻¹) heo k]
      exact norm_matchedMode_fieldWeight_channel_le D hP Eo.symm (fun r => (Wo s r)⁻¹)
        heo (A s) (hA s) (hA₀ s) (fun i r hr => (hlocal s i r hr).1) k
    have hin :
        ‖(Ei.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) :
          RadialModePair D →L[ℝ] RadialModePair D) ∘L matchedModeChannel D hP m‖ ≤ B s m :=
      norm_matchedMode_fieldWeight_channel_le D hP Ei (Wi s) hei
        (B s) (hB s) (hB₀ s) (fun i r hr => (hlocal s i r hr).2) m
    have hmid :
        ‖(Eo.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) :
            RadialModePair D →L[ℝ] RadialModePair D) ∘L T ∘L
          ((Ei.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).symm :
            RadialModePair D →L[ℝ] RadialModePair D)‖ ≤ C := hweighted s
    calc
      _ ≤ A s k * C * B s m :=
        matchedMode_twoWeight_block_bound
          (Eo.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
          (Ei.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
          (matchedModeChannel D hP k) T (matchedModeChannel D hP m)
          (hA s k) hC hout hmid hin
      _ = _ := by
        dsimp only [A, B]
        rw [show a * (radialQ (level k) + radialQ (level m)) - height s k + height s m =
          (a * radialQ (level k) - height s k) +
            (a * radialQ (level m) + height s m) by ring, Real.exp_add]
        ring
  by_cases hkm : radialS (level m) ≤ radialS (level k)
  · calc
      _ ≤ _ := hsign true
      _ = _ := by
        change C * R ^ 2 * Real.exp
          (a * (radialQ (level k) + radialQ (level m)) - radialS (level k) + radialS (level m)) =
          C * R ^ 2 * Real.exp
            (a * (radialQ (level k) + radialQ (level m)) - |radialS (level k) - radialS (level m)|)
        rw [abs_of_nonneg (sub_nonneg.mpr hkm)]
        congr 2
        ring
  · calc
      _ ≤ _ := hsign false
      _ = _ := by
        change C * R ^ 2 * Real.exp
          (a * (radialQ (level k) + radialQ (level m)) - (-radialS (level k)) - radialS (level m)) =
          C * R ^ 2 * Real.exp
            (a * (radialQ (level k) + radialQ (level m)) - |radialS (level k) - radialS (level m)|)
        rw [abs_of_nonpos (sub_nonpos.mpr (lt_of_not_ge hkm).le)]
        congr 2
        ring

end ContinuousFlexibility.Radial
