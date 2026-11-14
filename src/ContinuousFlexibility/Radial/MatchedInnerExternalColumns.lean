module

public import ContinuousFlexibility.Radial.MatchingInverseFormula
public import ContinuousFlexibility.Radial.MatchedInnerExternalDecomposition
public import ContinuousFlexibility.Radial.MatchedModeWeightedCells

/-!
# Spatial bounds for the actual external inner columns

The external-column identity is proved from its leading field and actual
residual. Two physical weight signs bound the correction through the
same matching inverse. Localizer bounds then select the sign giving
the full distance decay. No internal-interface Poisson vector is used
in place of an external matching column.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

section LeadingBound

variable {D : ReferenceData}
  (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
  {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
  (hm : M.innerLeft < M.innerRight) (hscale : ∀ k, 0 < M.boundaryScale k)
  (i : Fin 2) (L f : RadialModeL2 D) (u : ℝ → ℝ)
  (hEq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (L, 0) (f, 0))
  (hrow : (∫ r in D.a..D.b, referenceColumn D r * L r) = 0)
  (hu : (L : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
    (Ioo M.innerLeft M.innerRight)] u)
  (hz : (L : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
    (matchingOuterRegion D M)] fun _ => 0)
  (hreg : ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight))
  (htrace : ∀ k, u (matchingCut D M k) =
    (if i = k then 1 else 0) / Real.sqrt (M.boundaryScale k))

include hD hB hM hm hscale hEq hrow hu hz hreg htrace

/-- The weighted norm of the actual external column follows from the
proved leading/residual identity and a bound on the original inverse
with its original source restriction and scalar gate. -/
theorem matchedInnerPoisson_weighted_norm_le
    (Eo Ei : RadialModePair D ≃L[ℝ] RadialModePair D)
    {K A B : ℝ} (hK : 0 ≤ K)
    (hweighted : ‖(Eo : RadialModePair D →L[ℝ] RadialModePair D) ∘L M.innerInverse ∘L
      matchingSourceInnerCLM D M hM ∘L matchedModeScalarGate D (decide (M.frequency = 2)) ∘L
      (Ei.symm : RadialModePair D →L[ℝ] RadialModePair D)‖ ≤ K)
    (hL : ‖Eo ((L, 0) : RadialModePair D)‖ ≤ A)
    (hf : ‖Ei ((f, 0) : RadialModePair D)‖ ≤ B) :
    ‖Eo (M.innerPoisson i)‖ ≤ A + K * B := by
  let T : RadialModePair D →L[ℝ] RadialModePair D :=
    (Eo : RadialModePair D →L[ℝ] RadialModePair D) ∘L M.innerInverse ∘L
      matchingSourceInnerCLM D M hM ∘L matchedModeScalarGate D (decide (M.frequency = 2)) ∘L
      (Ei.symm : RadialModePair D →L[ℝ] RadialModePair D)
  have hgate :
      matchedModeScalarGate D (decide (M.frequency = 2)) ((f, 0) : RadialModePair D) =
        (f, 0) :=
    matchedModeScalarGate_eq_self D _ (f, 0) (fun _ => rfl)
  have happ : T (Ei ((f, 0) : RadialModePair D)) =
      Eo (M.innerInverse (M.sourceInner (f, 0))) := by
    simp only [T, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, hgate, matchingSourceInnerCLM_apply]
  have hrem : ‖Eo (M.innerInverse (M.sourceInner (f, 0)))‖ ≤ K * B := by
    rw [← happ]
    calc
      _ ≤ ‖T‖ * ‖Ei ((f, 0) : RadialModePair D)‖ := T.le_opNorm _
      _ ≤ K * B := mul_le_mul hweighted hf (norm_nonneg _) hK
  rw [matchedInnerPoisson_eq_leading_sub_inverse hD hB hM hm hscale
    i L f u hEq hrow hu hz hreg htrace, map_sub]
  exact (norm_sub_le _ _).trans (add_le_add hL hrem)

end LeadingBound

/-- A weighted actual vector has full spatial decay at the original
augmented cell channels. The source level n is the true transition
level when this is applied to an external matching column. -/
theorem matchedMode_twoSign_column_envelope
    (D : ReferenceData) (hP : RadialPartition D) (P : RadialModePair D) (n : ℕ)
    (W : Bool → ℝ → ℝ) (hW : ∀ s, Measurable (W s)) (hw : ∀ s r, 0 < W s r)
    (B V : Bool → ℝ)
    (hB : ∀ s r, |W s r| ≤ B s) (hV : ∀ s r, |(W s r)⁻¹| ≤ V s)
    {C R a : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hweighted : ∀ s : Bool,
      ‖matchedModeActualWeight D (W s) (hW s) (hw s) (B s) (V s) (hB s) (hV s) P‖ ≤
        C * Real.exp (a * radialQ n + (if s then radialS n else -radialS n)))
    (hlocal : ∀ s m r, r ∈ D.cells m →
      |(W s r)⁻¹| ≤ R * Real.exp
        (a * radialQ (D.cellIndex m) -
          (if s then radialS (D.cellIndex m) else -radialS (D.cellIndex m))))
    (k : ℕ) :
    ‖matchedModeChannel D hP k P‖ ≤ C * R * Real.exp
      (a * (radialQ (referenceRawChannelLevel D k) + radialQ n) -
        |radialS (referenceRawChannelLevel D k) - radialS n|) := by
  let level := referenceRawChannelLevel D
  let height : Bool → ℕ → ℝ := fun s j => if s then radialS j else -radialS j
  let A : Bool → ℕ → ℝ := fun s j => R * Real.exp (a * radialQ (level j) - height s (level j))
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hA : ∀ s j, 0 ≤ A s j := fun s j => mul_nonneg hR₀ (Real.exp_pos _).le
  have hq₀ : radialQ 0 = 0 := by norm_num [radialQ]
  have hs₀ : radialS 0 = 0 := by norm_num [radialS]
  have hA₀ : ∀ s, 1 ≤ A s 0 := by
    intro s
    simpa only [A, level, height, referenceRawChannelLevel, hq₀, hs₀, neg_zero,
      ite_self, mul_zero, sub_zero, Real.exp_zero, mul_one] using hR
  have hsign (s : Bool) :
      ‖matchedModeChannel D hP k P‖ ≤
        C * R * Real.exp (a * (radialQ (level k) + radialQ n) - height s (level k) + height s n) := by
    let E := innerWeightEquiv (radialHilbertMeasure D)
      (W s) (hW s) (hw s) (B s) (V s) (hB s) (hV s)
    let Em := E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
    have he : ∀ u, E.symm u =ᵐ[radialHilbertMeasure D] fun r => (W s r)⁻¹ * u r :=
      innerWeightEquiv_symm_ae (radialHilbertMeasure D) (W s) (hW s) (hw s)
        (B s) (V s) (hB s) (hV s)
    have hnorm :
        ‖matchedModeChannel D hP k ∘L (Em.symm : RadialModePair D →L[ℝ] RadialModePair D)‖ ≤
          A s k := by
      simp only [Em, ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.refl_symm]
      rw [← matchedMode_fieldWeight_commutes D hP E.symm (fun r => (W s r)⁻¹) he k]
      exact norm_matchedMode_fieldWeight_channel_le D hP E.symm (fun r => (W s r)⁻¹)
        he (A s) (hA s) (hA₀ s) (fun m r hr => hlocal s m r hr) k
    have hp : ‖Em P‖ ≤ C * Real.exp (a * radialQ n + height s n) := hweighted s
    calc
      _ = ‖(matchedModeChannel D hP k ∘L
          (Em.symm : RadialModePair D →L[ℝ] RadialModePair D)) (Em P)‖ := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply]
      _ ≤ ‖matchedModeChannel D hP k ∘L
          (Em.symm : RadialModePair D →L[ℝ] RadialModePair D)‖ * ‖Em P‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ A s k * (C * Real.exp (a * radialQ n + height s n)) :=
        mul_le_mul hnorm hp (norm_nonneg _) (hA s k)
      _ = _ := by
        dsimp only [A]
        rw [show a * (radialQ (level k) + radialQ n) - height s (level k) + height s n =
          (a * radialQ (level k) - height s (level k)) + (a * radialQ n + height s n) by ring]
        simp only [Real.exp_add]
        ring
  by_cases hkn : radialS n ≤ radialS (level k)
  · calc
      _ ≤ _ := hsign true
      _ = _ := by
        change C * R * Real.exp (a * (radialQ (level k) + radialQ n) - radialS (level k) + radialS n) =
          C * R * Real.exp (a * (radialQ (level k) + radialQ n) - |radialS (level k) - radialS n|)
        rw [abs_of_nonneg (sub_nonneg.mpr hkn)]
        congr 2
        ring
  · calc
      _ ≤ _ := hsign false
      _ = _ := by
        change C * R * Real.exp (a * (radialQ (level k) + radialQ n) - (-radialS (level k)) + (-radialS n)) =
          C * R * Real.exp (a * (radialQ (level k) + radialQ n) - |radialS (level k) - radialS n|)
        rw [abs_of_nonpos (sub_nonpos.mpr (lt_of_not_ge hkn).le)]
        congr 2
        ring

/-- Actual leading and residual estimates, together with the two bounds
for the original restricted inverse, give the actual external column
at every field or border channel. -/
theorem matchedInnerPoisson_twoSign_cell_envelope {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (hm : M.innerLeft < M.innerRight) (hscale : ∀ k, 0 < M.boundaryScale k)
    (i : Fin 2) (L f : RadialModeL2 D) (u : ℝ → ℝ)
    (hEq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (L, 0) (f, 0))
    (hrow : (∫ r in D.a..D.b, referenceColumn D r * L r) = 0)
    (hu : (L : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] u)
    (hz : (L : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] fun _ => 0)
    (hreg : ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight))
    (htrace : ∀ k, u (matchingCut D M k) =
      (if i = k then 1 else 0) / Real.sqrt (M.boundaryScale k))
    (Wo Wi : Bool → ℝ → ℝ)
    (hWo : ∀ s, Measurable (Wo s)) (hWi : ∀ s, Measurable (Wi s))
    (ho : ∀ s r, 0 < Wo s r) (hi : ∀ s r, 0 < Wi s r)
    (Bo Co Bi Ci : Bool → ℝ)
    (hBo : ∀ s r, |Wo s r| ≤ Bo s) (hCo : ∀ s r, |(Wo s r)⁻¹| ≤ Co s)
    (hBi : ∀ s r, |Wi s r| ≤ Bi s) (hCi : ∀ s r, |(Wi s r)⁻¹| ≤ Ci s)
    {K A B R a : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hweighted : ∀ s : Bool,
      ‖(matchedModeActualWeight D (Wo s) (hWo s) (ho s) (Bo s) (Co s) (hBo s) (hCo s) :
          RadialModePair D →L[ℝ] RadialModePair D) ∘L M.innerInverse ∘L
        matchingSourceInnerCLM D M hM ∘L matchedModeScalarGate D (decide (M.frequency = 2)) ∘L
        ((matchedModeActualWeight D (Wi s) (hWi s) (hi s) (Bi s) (Ci s) (hBi s) (hCi s)).symm :
          RadialModePair D →L[ℝ] RadialModePair D)‖ ≤ K)
    (hL : ∀ s : Bool,
      ‖matchedModeActualWeight D (Wo s) (hWo s) (ho s) (Bo s) (Co s) (hBo s) (hCo s)
        ((L, 0) : RadialModePair D)‖ ≤ A * Real.exp
          (a * radialQ M.transitionIndex +
            (if s then radialS M.transitionIndex else -radialS M.transitionIndex)))
    (hf : ∀ s : Bool,
      ‖matchedModeActualWeight D (Wi s) (hWi s) (hi s) (Bi s) (Ci s) (hBi s) (hCi s)
        ((f, 0) : RadialModePair D)‖ ≤ B * Real.exp
          (a * radialQ M.transitionIndex +
            (if s then radialS M.transitionIndex else -radialS M.transitionIndex)))
    (hlocal : ∀ s m r, r ∈ D.cells m →
      |(Wo s r)⁻¹| ≤ R * Real.exp
        (a * radialQ (D.cellIndex m) -
          (if s then radialS (D.cellIndex m) else -radialS (D.cellIndex m))))
    (k : ℕ) :
    ‖matchedModeChannel D hD.choose_spec.2.1 k (M.innerPoisson i)‖ ≤
      (A + K * B) * R * Real.exp
        (a * (radialQ (referenceRawChannelLevel D k) + radialQ M.transitionIndex) -
          |radialS (referenceRawChannelLevel D k) - radialS M.transitionIndex|) := by
  apply matchedMode_twoSign_column_envelope D hD.choose_spec.2.1 (M.innerPoisson i)
    M.transitionIndex Wo hWo ho Bo Co hBo hCo (add_nonneg hA (mul_nonneg hK hB)) hR
    ?_ hlocal k
  intro s
  have hh := matchedInnerPoisson_weighted_norm_le hD hborder hM hm hscale
    i L f u hEq hrow hu hz hreg htrace
    (matchedModeActualWeight D (Wo s) (hWo s) (ho s) (Bo s) (Co s) (hBo s) (hCo s))
    (matchedModeActualWeight D (Wi s) (hWi s) (hi s) (Bi s) (Ci s) (hBi s) (hCi s))
    hK (hweighted s) (hL s) (hf s)
  convert hh using 1 <;> ring

end ContinuousFlexibility.Radial
