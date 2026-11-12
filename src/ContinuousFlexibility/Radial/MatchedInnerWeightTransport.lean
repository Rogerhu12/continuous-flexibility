import ContinuousFlexibility.Radial.MatchingInverseFormula
import ContinuousFlexibility.Radial.MatchedInnerActualSource
import ContinuousFlexibility.Radial.MatchedModeWeightedCells
import ContinuousFlexibility.Radial.InnerSupportedWeights

/-!
# From the same supported inner inverse to the original mode-pair norm

The source restriction is the original M.sourceInner function. It
commutes with actual weights and is a contraction. Supported weights are
restrictions of the same full field multipliers. Thus a weighted bound
for C.inverse transfers to M.innerInverse on its actual restricted
sources, including the frequency-dependent scalar gate. The only
change of norm costs sqrt 2.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem matchedInner_sourceInner_norm_le {D : ReferenceData}
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (F : RadialModePair D) : ‖M.sourceInner F‖ ≤ ‖F‖ := by
  have hf : ‖(M.sourceInner F).1‖ ≤ ‖F.1‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hM.2.2.2.1 F).2.2.1] with r hr
    rw [hr]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (F.1 r)
  rw [Prod.norm_def, Prod.norm_def, (hM.2.2.2.1 F).1]
  exact max_le_max hf le_rfl

/-- The original restriction commutes with any actual field multiplier.
No linear-map structure is imposed on its frozen function type. -/
theorem matchedInner_sourceInner_weight_commute {D : ReferenceData}
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (w : ℝ → ℝ)
    (hE : ∀ u, E u =ᵐ[radialHilbertMeasure D] fun r => w r * u r)
    (F : RadialModePair D) :
    M.sourceInner (E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) F) =
      E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) (M.sourceInner F) := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(hM.2.2.2.1 (E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) F)).2.2.1,
      (hM.2.2.2.1 F).2.2.1, hE F.1, hE (M.sourceInner F).1]
      with r hleft hsource hinput hright
    change (M.sourceInner (E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) F)).1 r =
      E (M.sourceInner F).1 r
    rw [hleft, hright, hsource]
    change (if r ∈ Ioo M.innerLeft M.innerRight then E F.1 r else 0) =
      w r * (if r ∈ Ioo M.innerLeft M.innerRight then F.1 r else 0)
    rw [hinput]
    split_ifs <;> simp only [mul_zero]
  · change (M.sourceInner (E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) F)).2 =
      (M.sourceInner F).2
    rw [(hM.2.2.2.1 _).1, (hM.2.2.2.1 F).1]
    rfl

private theorem matchedInner_scalarGate_norm_le (D : ReferenceData) (active : Bool)
    (F : RadialModePair D) : ‖matchedModeScalarGate D active F‖ ≤ ‖F‖ := by
  cases active with
  | false =>
    rw [matchedModeScalarGate_apply]
    change ‖(F.1, (0 : ℝ))‖ ≤ ‖F‖
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
    exact le_max_left _ _
  | true =>
    rw [matchedModeScalarGate_apply]
    exact le_rfl

private theorem matchedInner_scalarGate_weight (D : ReferenceData) (active : Bool)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (F : RadialModePair D) :
    matchedModeScalarGate D active (E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) F) =
      E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) (matchedModeScalarGate D active F) := by
  cases active <;> rfl

section ActualTransfer

variable {D : ReferenceData}
  (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
  (hw : ContDiff ℝ ∞ D.w) {n : ℕ} (G : InnerRadialChainGeometry D n)
  (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
  (hleft : M.innerLeft = G.left 0) (hright : M.innerRight = G.right (Fin.last n))
  (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
  (central : Fin (n + 1)) (column : RadialModeL2 D)
  (hcolumn : column = matchingBorderVector D hD hB)
  (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
    (Ioo (G.left central) (G.right central)) column = column)
  (C : InnerRadialActualChain D G (decide (M.frequency = 2))
    (M.frequency : ℝ) central column)
  (hS : IsUnit C.fluxMatrix)
  (Wo Wi : ℝ → ℝ) (hWo : Measurable Wo) (hWi : Measurable Wi)
  (ho : ∀ r, 0 < Wo r) (hi : ∀ r, 0 < Wi r)
  (Bo Co Bi Ci : ℝ)
  (hBo : ∀ r, |Wo r| ≤ Bo) (hCo : ∀ r, |(Wo r)⁻¹| ≤ Co)
  (hBi : ∀ r, |Wi r| ≤ Bi) (hCi : ∀ r, |(Wi r)⁻¹| ≤ Ci)

local notation "H" => InnerRadialPhysicalSource D G (decide (M.frequency = 2))
local notation "Eo" => innerWeightEquiv (radialHilbertMeasure D) Wo hWo ho Bo Co hBo hCo
local notation "Ei" => innerWeightEquiv (radialHilbertMeasure D) Wi hWi hi Bi Ci hBi hCi
local notation "Ho" => innerSupportedWeightEquiv (radialHilbertMeasure D)
  (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
  (decide (M.frequency = 2)) Wo hWo ho Bo Co hBo hCo
local notation "Hi" => innerSupportedWeightEquiv (radialHilbertMeasure D)
  (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
  (decide (M.frequency = 2)) Wi hWi hi Bi Ci hBi hCi
local notation "Mo" => matchedModeActualWeight D Wo hWo ho Bo Co hBo hCo
local notation "Mi" => matchedModeActualWeight D Wi hWi hi Bi Ci hBi hCi

include hD hB hM hleft hright hsub hcolumn hcolfix

/-- A bound on the same supported C.inverse gives a bound on the original
restricted matching inverse. Arbitrary extensions of the positive
weights outside the finite inner region give the same restricted
action; in particular the usual extension by one is covered. -/
theorem matchedInnerActualInverse_weighted_apply_le
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ‖(Ho : H →L[ℝ] H) ∘L C.inverse hw hS ∘L ((Hi).symm : H →L[ℝ] H)‖ ≤ K)
    (F : RadialModePair D) :
    ‖Mo (M.innerInverse (M.sourceInner
      (matchedModeScalarGate D (decide (M.frequency = 2)) ((Mi).symm F))))‖ ≤
        Real.sqrt 2 * K * ‖F‖ := by
  let Fgate := matchedModeScalarGate D (decide (M.frequency = 2)) F
  have hgateAdmissible : M.frequency ≠ 2 → Fgate.2 = 0 := by
    intro hj
    simp [Fgate, matchedModeScalarGate_apply, hj]
  let Z : H := ⟨WithLp.toLp 2 (M.sourceInner Fgate),
    matchedInner_sourceInner_mem hD G M hM hleft hright Fgate hgateAdmissible⟩
  have hsource : ‖Z‖ ≤ Real.sqrt 2 * ‖F‖ := by
    have hs := innerBorder_norm_le_sqrt_two_mul Z.val
    change ‖Z‖ ≤ Real.sqrt 2 * ‖WithLp.ofLp Z.val‖ at hs
    have hnorm : ‖WithLp.ofLp Z.val‖ ≤ ‖F‖ := by
      change ‖M.sourceInner Fgate‖ ≤ ‖F‖
      exact (matchedInner_sourceInner_norm_le M hM Fgate).trans
        (matchedInner_scalarGate_norm_le D _ F)
    exact hs.trans (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg 2))
  have hei : ∀ u, (Ei).symm u =ᵐ[radialHilbertMeasure D] fun r => (Wi r)⁻¹ * u r :=
    innerWeightEquiv_symm_ae (radialHilbertMeasure D) Wi hWi hi Bi Ci hBi hCi
  have hgate :
      matchedModeScalarGate D (decide (M.frequency = 2)) ((Mi).symm F) =
        (Mi).symm Fgate :=
    matchedInner_scalarGate_weight D _ (Ei).symm F
  have hin :
      (((Hi).symm Z).val.fst, ((Hi).symm Z).val.snd) =
        M.sourceInner (matchedModeScalarGate D (decide (M.frequency = 2)) ((Mi).symm F)) := by
    rw [innerSupportedWeightEquiv_symm_apply, innerBorderWeightEquiv_symm_apply]
    change (Mi).symm (M.sourceInner Fgate) =
      M.sourceInner (matchedModeScalarGate D (decide (M.frequency = 2)) ((Mi).symm F))
    calc
      _ = M.sourceInner ((Mi).symm Fgate) :=
        (matchedInner_sourceInner_weight_commute M hM (Ei).symm (fun r => (Wi r)⁻¹) hei Fgate).symm
      _ = _ := congrArg M.sourceInner hgate.symm
  have hmodel := matchedInnerActualInverse_eq_innerInverse hD hB hw G M
    hleft hright hsub central column hcolumn hcolfix C hS hM ((Hi).symm Z)
  rw [hin] at hmodel
  have hout :
      Mo (M.innerInverse (M.sourceInner
        (matchedModeScalarGate D (decide (M.frequency = 2)) ((Mi).symm F)))) =
      ((Ho (C.inverse hw hS ((Hi).symm Z))).val.fst,
        (Ho (C.inverse hw hS ((Hi).symm Z))).val.snd) := by
    rw [hmodel, innerSupportedWeightEquiv_apply, innerBorderWeightEquiv_apply]
    rfl
  rw [hout]
  calc
    _ ≤ ‖Ho (C.inverse hw hS ((Hi).symm Z))‖ :=
      innerBorder_ofLp_norm_le _
    _ ≤ K * ‖Z‖ :=
      (((Ho : H →L[ℝ] H) ∘L C.inverse hw hS ∘L ((Hi).symm : H →L[ℝ] H)).le_opNorm Z).trans
        (mul_le_mul_of_nonneg_right hbound (norm_nonneg Z))
    _ ≤ K * (Real.sqrt 2 * ‖F‖) :=
      mul_le_mul_of_nonneg_left hsource hK
    _ = _ := by ring

/-- The same bound in the existing source CLM representation, directly
usable for localized matching blocks. The non-j=2 scalar remains gated. -/
theorem matchedInnerActualInverse_weighted_opNorm_le
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ‖(Ho : H →L[ℝ] H) ∘L C.inverse hw hS ∘L ((Hi).symm : H →L[ℝ] H)‖ ≤ K) :
    ‖(Mo : RadialModePair D →L[ℝ] RadialModePair D) ∘L M.innerInverse ∘L
      matchingSourceInnerCLM D M hM ∘L matchedModeScalarGate D (decide (M.frequency = 2)) ∘L
      ((Mi).symm : RadialModePair D →L[ℝ] RadialModePair D)‖ ≤ Real.sqrt 2 * K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg 2) hK)
  intro F
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    matchingSourceInnerCLM_apply] using
    matchedInnerActualInverse_weighted_apply_le hD hB hw G M hM hleft hright hsub
      central column hcolumn hcolfix C hS Wo Wi hWo hWi ho hi Bo Co Bi Ci
      hBo hCo hBi hCi hK hbound F

end ActualTransfer

end ContinuousFlexibility.Radial
