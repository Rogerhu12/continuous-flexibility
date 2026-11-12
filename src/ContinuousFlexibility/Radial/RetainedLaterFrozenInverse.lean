import ContinuousFlexibility.Radial.RetainedFixedCentralInverse

/-!
# The actual later-band inverse with the fixed exponent thirty-eight

The numerical threshold is chosen after Cstar but before the selected
tail or the retained pair. Actual finite-chain inversion then supplies
the original frozen modal graph, with its unchanged source and scalar,
and a representative for every ambient source.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.L2Operator

theorem exists_fixedCentralLaterBudgetStart (T B₀ C₀ K₀ CM Cstar : ℝ)
    (hC₀ : 0 ≤ C₀) (hCM : 0 ≤ CM) (hCstar : 0 ≤ Cstar) (initial : ℕ) :
    ∃ N : ℕ, initial ≤ N ∧ ∀ (chain : MorseChainData) (n j : ℕ), N ≤ n →
      chain.d n = morseChainInteger n → radialFrequencyBand chain Cstar n j →
      sqrt 2 * (fixedCentralLaterDirichletCoefficient T B₀ C₀ CM * radialE n ^ (37 : ℝ) +
        8 * (fixedCentralLaterPoissonCoefficient T B₀ C₀ K₀) ^ 2 * (1 + (j : ℝ)) ^ 4 +
        96 + 48 * fixedCentralLaterEndpointCoefficient C₀ CM) ≤ radialE n ^ (38 : ℝ) := by
  have hp : 0 ≤ sqrt 2 * 8 * (fixedCentralLaterPoissonCoefficient T B₀ C₀ K₀) ^ 2 :=
    mul_nonneg (mul_nonneg (sqrt_nonneg 2) (by norm_num)) (sq_nonneg _)
  have hL : 0 ≤ fixedCentralLaterEndpointCoefficient C₀ CM := by
    unfold fixedCentralLaterEndpointCoefficient retainedMorseEndpointCoefficient
    exact add_nonneg (mul_nonneg (by norm_num) hCM)
      (mul_nonneg (mul_nonneg (by norm_num) hC₀) centralRadiusWeightConstant_pos.le)
  have hr : 0 ≤ sqrt 2 * (96 + 48 * fixedCentralLaterEndpointCoefficient C₀ CM) :=
    mul_nonneg (sqrt_nonneg 2) (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hL))
  obtain ⟨N, hN, hbound⟩ := exists_inner_later_budget_start
    (d := sqrt 2 * fixedCentralLaterDirichletCoefficient T B₀ C₀ CM) hCstar hp hr initial
  refine ⟨N, hN, ?_⟩
  intro chain n j hn hd hband
  calc
    _ = (sqrt 2 * fixedCentralLaterDirichletCoefficient T B₀ C₀ CM) *
        radialE n ^ (37 : ℝ) +
      (sqrt 2 * 8 * (fixedCentralLaterPoissonCoefficient T B₀ C₀ K₀) ^ 2) *
        (1 + (j : ℝ)) ^ 4 +
      sqrt 2 * (96 + 48 * fixedCentralLaterEndpointCoefficient C₀ CM) := by ring
    _ ≤ _ := hbound chain n j hn hd hband

def fixedCentralLaterBudgetStart (T B₀ C₀ K₀ CM Cstar : ℝ)
    (hC₀ : 0 ≤ C₀) (hCM : 0 ≤ CM) (hCstar : 0 ≤ Cstar) (initial : ℕ) : ℕ :=
  Classical.choose (exists_fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM Cstar
    hC₀ hCM hCstar initial)

theorem fixedCentralLaterBudgetStart_spec (T B₀ C₀ K₀ CM Cstar : ℝ)
    (hC₀ : 0 ≤ C₀) (hCM : 0 ≤ CM) (hCstar : 0 ≤ Cstar) (initial : ℕ) :
    initial ≤ fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM Cstar hC₀ hCM hCstar initial ∧
      ∀ (chain : MorseChainData) (n j : ℕ),
        fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM Cstar hC₀ hCM hCstar initial ≤ n →
        chain.d n = morseChainInteger n → radialFrequencyBand chain Cstar n j →
        sqrt 2 * (fixedCentralLaterDirichletCoefficient T B₀ C₀ CM * radialE n ^ (37 : ℝ) +
          8 * (fixedCentralLaterPoissonCoefficient T B₀ C₀ K₀) ^ 2 * (1 + (j : ℝ)) ^ 4 +
          96 + 48 * fixedCentralLaterEndpointCoefficient C₀ CM) ≤ radialE n ^ (38 : ℝ) :=
  Classical.choose_spec (exists_fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM Cstar
    hC₀ hCM hCstar initial)

theorem even_frequency_half {j : ℕ} (hj : 2 ≤ j) (heven : Even j) :
    1 ≤ j / 2 ∧ j = 2 * (j / 2) := by
  obtain ⟨q, hq⟩ := heven
  omega

/-- The inverse is for the original matching datum and the same
source projection. The data assumed about localized models are exactly
the raw witnesses supplied before the physical reference is chosen. -/
theorem SeedRetainedPair.exists_later_inner_inverse {S : SelectedTailData}
    {K : SeedCentralCutoff} {headLength length : ℝ}
    (P : SeedRetainedPair S K headLength length)
    (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hhead : 0 < headLength)
    (hbridge : ∀ side r, r ∈ uIcc (S.cut side S.chain.index)
      (S.entry side S.chain.index) → 0 < deriv (S.family S.sigma).w r)
    (hjoin : ∀ side n, S.chain.index < n →
      S.joinInner side n = r07PreviousCellJoin S.chain side (n - 1))
    (B : FixedCentralBorder) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    {T B₀ C₀ K₀ CM KM : ℝ} (hT : 8 ≤ T)
    (hcap : sqrt centralOscillatorA + 2 ≤ T)
    (hC₀ : 0 < C₀) (hK₀ : 0 ≤ K₀) (hCM : 0 < CM) (hCstar : 0 ≤ S.Cstar)
    (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
      (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
    (hcolumn : referenceColumn Γ.reference = fixedCentralColumn B.chi)
    (initial : ℕ)
    (hstart : fixedCentralLaterBudgetStart T B₀ C₀ K₀ CM S.Cstar
      hC₀.le hCM.le hCstar initial ≤ S.chain.index)
    (hN : 4096 ≤ S.chain.index) (k : ℕ) (hk : 0 < k) (qf : ℕ) (hqf : 1 ≤ qf)
    (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + k) (2 * qf))
    (hB₀ : BufferHypotheses (B.modelBuffer qf T B₀))
    (M₀ : InnerBufferLocalizedData (B.modelBuffer qf T B₀) C₀ K₀)
    (henergy : ∀ i, 0 < fixedCentralModelCutEnergy M₀ i ∧
      (M₀.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M₀ i)
    (herror₀ : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa M₀) (fun _ => 1)
        (M₀.physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer qf T B₀) i))) sign‖ ≤
        (1 : ℝ) / 8)
    (hB : ∀ side p, BufferHypotheses
      (innerMorseBufferData
        (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
        (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
        (2 * (qf : ℝ)) (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)))
    (models : ∀ side p, InnerBufferLocalizedData
      (innerMorseBufferData
        (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
        (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
        (2 * (qf : ℝ)) (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)) CM KM)
    (hrem : ∀ side p i, innerMorseModelNormalizedRemainder (models side p) i ≤
      1 / (2 * (qf : ℝ)))
    (herror : ∀ side p height, 0 < height → ∀ sign : Bool,
      ‖innerTwoCutWeightedError
        (innerPhysicalCutKappa height (fun _ => 1)
          (fun i => ((models side p).column i).inwardEnergy))
        (innerMorseCutWeight S.chain.index 0 0 side
          (innerMorseInnerTailIndex S.chain.index k side p))
        ((models side p).physicalFluxError height (fun _ => 1)) sign‖ ≤ (1 : ℝ) / 8)
    (M : RadialMatchingData Γ.reference) (hfrequency : M.frequency = 2 * qf)
    (hML : M.innerLeft = P.sideRadius false * S.joinInner false (S.chain.index + k))
    (hMR : M.innerRight = P.sideRadius true * S.joinInner true (S.chain.index + k))
    (hsource : M.sourceInner = modeInnerSource Γ.reference M.innerLeft M.innerRight) :
    ∃ A : RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference,
    ∃ u : RadialModePair Γ.reference → ℝ → ℝ,
      ‖A‖ ≤ radialE (S.chain.index + k) ^ (38 : ℝ) ∧
      (∀ F, A (M.sourceInner F) = A F) ∧
      (∀ F, (M.frequency ≠ 2 → F.2 = 0) →
        ModeInnerDirichletGraph Γ.reference M (A (M.sourceInner F)) (M.sourceInner F)) ∧
      (∀ U F, ModeInnerDirichletGraph Γ.reference M U F → A F = U) ∧
      ∀ F, ((A (M.sourceInner F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure Γ.reference] u F ∧
        ModeLocalEquation Γ.reference M.frequency (Ioo M.innerLeft M.innerRight)
          (A (M.sourceInner F)) (M.sourceInner F) ∧
        ContDiffOn ℝ 1 (u F) (Icc M.innerLeft M.innerRight) ∧
        (∀ r ∈ matchingOuterRegion Γ.reference M, u F r = 0) ∧
        (if M.frequency = 2 then
          (∫ r in Γ.reference.a..Γ.reference.b, referenceColumn Γ.reference r * u F r) = F.2
         else (A (M.sourceInner F)).2 = 0) ∧
        ∀ i, u F (matchingCut Γ.reference M i) = 0 := by
  have hAcc : IsAccumulatingProfile Γ.reference := hΓ.2.1
  have hb : RadialTrueBorder Γ.reference := hΓ.2.2.1
  have hD : RadialProfileGeometry Γ.reference := (Classical.choose_spec hAcc).1
  have hTpos : 0 < T := (by norm_num : (0 : ℝ) < 8).trans_le hT
  let H := P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hhead hTpos
    hleft hright hTL hTR k hk
  let center := innerModelChainPiece (innerMorseInnerCenter k)
  have hends := P.retainedMorseInnerGeometry_outer hD hw hS G₀ hfirst hhead hTpos
    hleft hright hTL hTR k hk hjoin
  have hHL : H.left 0 = M.innerLeft := hends.1.trans hML.symm
  have hHR : H.right (Fin.last (2 * (2 * k + 1))) = M.innerRight := hends.2.trans hMR.symm
  have hLcore : H.left 0 ∈ radialCore Γ.reference :=
    radialCore_mem_of_profile_pos hD (H.weight_pos 0 _ (left_mem_Icc.mpr (H.left_lt_right 0).le))
  have hRcore : H.right (Fin.last (2 * (2 * k + 1))) ∈ radialCore Γ.reference :=
    radialCore_mem_of_profile_pos hD (H.weight_pos _ _ (right_mem_Icc.mpr (H.left_lt_right _).le))
  have hab : M.innerLeft < M.innerRight := by
    rw [← hHL, ← hHR]
    apply H.increasing
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_zero, Fin.val_succ, Fin.val_last]
    omega
  have hsub : Icc M.innerLeft M.innerRight ⊆ radialCore Γ.reference := by
    intro r hr
    rw [← hHL, ← hHR] at hr
    exact ⟨hLcore.1.trans_le hr.1, hr.2.trans_lt hRcore.2⟩
  have hbool : centralModelBordered qf = decide (M.frequency = 2) := by
    by_cases hq1 : qf = 1
    · simp [centralModelBordered, hq1, hfrequency]
    · have hf : M.frequency ≠ 2 := by omega
      simp [centralModelBordered, hq1, hf]
  have hfreq : (M.frequency : ℝ) = 2 * (qf : ℝ) := by exact_mod_cast hfrequency
  have hex := P.exists_retainedFixedCentralInverse hD hAcc hb hw hS G₀ hfirst hhead hT
    hleft hright hTL hTR k hk hbridge hmodel hwindow B qf hqf hcap hcolumn hB₀ M₀ hB models
    hN hC₀ hK₀ hCM henergy herror₀ hrem herror
  rw [hbool] at hex
  obtain ⟨inverse, hgraph, _, hnorm⟩ := hex
  have hsolve : ∀ F, InnerRadialPhysicalWeakGraph Γ.reference hD.2.2.1.1.continuous H
      (decide (M.frequency = 2)) (M.frequency : ℝ) center
      (matchingBorderVector Γ.reference hAcc hb) (inverse F) F := by
    intro F
    rw [hfreq]
    exact (hgraph (inverse F) F).mpr rfl
  have hcentral := P.retainedMorseInnerGeometry_center hD hw hS G₀ hfirst hhead hTpos
    hleft hright hTL hTR k hk
  have hgs : Function.support (referenceColumn Γ.reference) ⊆
      Ioo (H.left center) (H.right center) := by
    rw [hcentral.1, hcentral.2, hcolumn]
    exact B.column_support_in_model hcap
  have hcolAE := matchingBorderVector_coe hAcc hb
  have hcost := (fixedCentralLaterBudgetStart_spec T B₀ C₀ K₀ CM S.Cstar
    hC₀.le hCM.le hCstar initial).2 S.chain (S.chain.index + k) (2 * qf)
    (hstart.trans (Nat.le_add_right _ _))
    ((hS.2.2.2.1 S.sigma hS.2.2.1).1.d_eq _ (Nat.le_add_right _ _)) hband
  have hnorm' : ‖InnerRadialPhysicalInverse.pairInverse inverse hAcc‖ ≤
      radialE (S.chain.index + k) ^ (38 : ℝ) := by
    exact hnorm.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcost)
  let A := InnerRadialPhysicalInverse.pairInverse inverse hAcc
  let u := InnerRadialPhysicalInverse.frozenRepresentative inverse hAcc hb hD.2.2.1.1 hsolve
    hHL hHR hab hsub hcolAE hgs
  refine ⟨A, u, hnorm', ?_, ?_, ?_, ?_⟩
  · intro F
    rw [hsource, ← hHL, ← hHR]
    exact InnerRadialPhysicalInverse.pairInverse_innerSource inverse hAcc F
  · intro F hF
    rw [hsource]
    exact InnerRadialPhysicalInverse.pairInverse_right_frozen inverse hAcc hb hD.2.2.1.1
      hsolve hHL hHR hab hsub hcolAE hgs F hF
  · intro U F hU
    exact InnerRadialPhysicalInverse.pairInverse_left_frozen inverse hAcc hb hD.2.2.1.1
      hsolve hHL hHR hab hsub hcolAE hgs hU
  · intro F
    rw [hsource]
    exact InnerRadialPhysicalInverse.frozenRepresentative_spec inverse hAcc hb hD.2.2.1.1
      hsolve hHL hHR hab hsub hcolAE hgs F

end ContinuousFlexibility.Radial
