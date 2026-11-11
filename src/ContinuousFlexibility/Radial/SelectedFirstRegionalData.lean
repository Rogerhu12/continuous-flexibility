import ContinuousFlexibility.Radial.SelectedFirstInnerInverse
import ContinuousFlexibility.Radial.SelectedTerminalMatching
import ContinuousFlexibility.Radial.SelectedTerminalOuterSupply
import ContinuousFlexibility.Radial.SelectedRetainedOuterSupply
import ContinuousFlexibility.Radial.SelectedFirstOuterPoisson
import ContinuousFlexibility.Radial.SelectedFirstCutoffGeometry
import ContinuousFlexibility.Radial.TerminalConeMatrixBudget
import ContinuousFlexibility.Radial.TerminalRegionalData

/-!
# Actual regional matching data throughout the first frequency band

The central model and its inverse cost precede the retained-cone length.
The natural representatives and their margin were also fixed on the original
selected tail. This construction uses their actual radius transports, the
actual growing incoming solutions, and the same reference on both sides.

The outer supplier is a local assembly interface. It installs the proved
outer inverse and its Poisson columns without changing any geometric,
boundary or source field. The inner inverse is constructed here from the
fixed central localized model; it is not an abstract input to this theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.L2Operator

/-- The common matching shell with the already selected natural family. -/
def SeedRetainedPair.firstTerminalMatching {S : SelectedTailData}
    {K : SeedCentralCutoff} {headLength length : ℝ}
    (P : SeedRetainedPair S K headLength length) (D : ReferenceData)
    (j : ℕ) (margin : ℝ) (v : Bool → ℝ → ℝ) : RadialMatchingData D :=
  selectedTerminalMatching D j S.chain.index margin
    (fun side => P.sideRadius side * S.joinInner side S.chain.index)
    (fun _ => 1 / (j : ℝ))
    (fun side => outerUnitState (selectedBoundaryState D j (r07OutwardSign side)
      (P.sideRadius side * S.joinInner side S.chain.index)
      (radialRadiusScale (P.sideRadius side) 1 (v side))))

/-- The first-band shell receives the actual outer construction for its
already chosen natural family; no outer existence hypothesis remains. -/
theorem SeedRetainedPair.firstTerminal_outerSupply {S : SelectedTailData}
    {K : SeedCentralCutoff} {headLength length : ℝ}
    (P : SeedRetainedPair S K headLength length)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hends : ∀ sigma tau, (S.family sigma).a = (S.family tau).a ∧
      (S.family sigma).b = (S.family tau).b)
    (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hcut : ∀ right n, S.chain.index < n →
      S.cut right n = r07PreviousCellCut S.chain right (n - 1))
    (hhead : 0 < headLength)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (f : R07FirstFrequency S.chain S.Cstar) (v : Bool → ℝ → ℝ) {η : ℝ}
    (hv : ∀ side, SelectedFirstNaturalData S side f.1 (v side) ∧
      2 * η ≤ selectedFirstBoundaryMargin S side f.1 (v side)) :
    SelectedTerminalOuterSupply (P.firstTerminalMatching Γ.reference f.1 η v) := by
  have hD : RadialProfileGeometry Γ.reference := (Classical.choose_spec hΓ.2.1).1
  have hdata (side : Bool) := P.selected_first_fixed_natural_data hD hw hS side f
    (hv side).1 (hv side).2
  obtain ⟨hLC, hCI, hIL, hLR, hRI, hIC, hCJ⟩ :=
    P.first_matching_order hS hfirst hhead hleft hright
  have horder : P.sideRadius false * S.joinInner false S.chain.index <
      P.sideRadius true * S.joinInner true S.chain.index :=
    hLC.trans (hCI.trans (hIL.trans (hLR.trans (hRI.trans (hIC.trans hCJ)))))
  exact P.selectedTerminal_outerSupply hΓ.2.1 hΓ.2.2.1 hw hS G hends hentry hfirst hcut
    f.2.1 f.2.2.1 f.2.2.2 (fun side => radialRadiusScale (P.sideRadius side) 1 (v side))
    (fun side => (hdata side).2.1) (fun side => (hdata side).2.2.1)
    horder η (fun _ => 1 / (f.1 : ℝ))

/-- Convert the actual first-cone estimates to the normalization used by
the regional record, retaining the complete matching interval in the energy. -/
theorem SeedRetainedPair.first_terminal_cutoff_estimates {S : SelectedTailData}
    {K : SeedCentralCutoff} {headLength length H ε : ℝ}
    (P : SeedRetainedPair S K headLength length)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile) (hS : IsSelectedTail S)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hhead : 0 < headLength)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (hcone : ∀ side, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ uIcc (S.cut side S.chain.index)
      (S.joinInner side S.chain.index), (S.family S.sigma).w =ᶠ[𝓝 x] (fun t => c * t))
    {j : ℕ} (hj : 2 ≤ j) (U : ∀ side, SeedPhysicalFirstIncoming P Γ.reference side j)
    (hH : 2 * log 2 < H) (hL : H < length) (hε : 0 ≤ ε)
    (hsource : terminalConeSourceConstant * exp (-((j : ℝ) * H / 2)) ≤
      sqrt (1 / (j : ℝ)) * ε)
    (henergy : (1 / (j : ℝ)) * (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) *
      exp (-((j : ℝ) * H)) ≤ (1 / (j : ℝ)) * ε) :
    let cut := fun side => P.sideRadius side * S.joinInner side S.chain.index
    let lam := fun side => standInBoundaryScale ((j : ℝ) ^ 2)
      (Γ.reference.w (cut side)) (cut side)
    ∀ side,
      MemLp (terminalCapHilbertSource (lam side) Γ.reference.w
        (P.firstTerminalCutoff H side) (U side).solution) 2
        (radialHilbertMeasure Γ.reference) ∧
      (eLpNorm (terminalCapHilbertSource (lam side) Γ.reference.w
        (P.firstTerminalCutoff H side) (U side).solution) 2
        (radialHilbertMeasure Γ.reference)).toReal ≤ ε * sqrt (1 / (j : ℝ)) ∧
      |(∫ r in cut false..cut true, terminalCapCutoffEnergy Γ.reference.w
        (P.firstTerminalCutoff H side) (U side).solution r) / lam side| ≤
          ε * (1 / (j : ℝ)) := by
  have hD : RadialProfileGeometry Γ.reference := (Classical.choose_spec hΓ.2.1).1
  have hlog : log 2 < H := (by linarith [log_pos (by norm_num : (1 : ℝ) < 2)])
  obtain ⟨hLC, hCI, hIL, hLR, hRI, hIC, hCJ⟩ :=
    P.first_matching_order hS hfirst hhead hleft hright
  dsimp only
  intro side
  obtain ⟨ha, hinside, hmem, hsrc, hene⟩ :=
    P.first_cutoff_source_energy hD hw hS hfirst side (hcone side) hj (U side)
      hH.le hlog hL
  have hlo : P.sideRadius false * S.joinInner false S.chain.index ≤
      P.firstTerminalLayer H side := by
    cases side
    · change P.sideRadius false * S.cut false S.chain.index <
        P.firstTerminalLayer H false ∧
        2 * P.firstTerminalLayer H false < P.sideRadius false * (P.side false).inner at hinside
      exact (hLC.trans hinside.1).le
    · change P.sideRadius true * (P.side true).inner < P.firstTerminalLayer H true ∧
        2 * P.firstTerminalLayer H true < P.sideRadius true * S.cut true S.chain.index at hinside
      exact (hLC.trans (hCI.trans (hIL.trans (hLR.trans (hRI.trans hinside.1))))).le
  have hhi : 2 * P.firstTerminalLayer H side ≤
      P.sideRadius true * S.joinInner true S.chain.index := by
    cases side
    · change P.sideRadius false * S.cut false S.chain.index <
        P.firstTerminalLayer H false ∧
        2 * P.firstTerminalLayer H false < P.sideRadius false * (P.side false).inner at hinside
      exact (hinside.2.trans (hIL.trans (hLR.trans (hRI.trans (hIC.trans hCJ))))).le
    · change P.sideRadius true * (P.side true).inner < P.firstTerminalLayer H true ∧
        2 * P.firstTerminalLayer H true < P.sideRadius true * S.cut true S.chain.index at hinside
      exact (hinside.2.trans hCJ).le
  refine ⟨hmem, ?_, ?_⟩
  · apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hε (sqrt_nonneg _))
    exact hsrc.trans (ENNReal.ofReal_le_ofReal (by simpa only [mul_comm] using hsource))
  · obtain ⟨hnonneg, hbound⟩ := hene _ _ hlo hhi
    rw [abs_of_nonneg hnonneg]
    exact hbound.trans (by simpa only [mul_comm] using henergy)

/-- Install the actual three-piece inverse and the actual first-band
cutoffs. The only regional supplier argument concerns the outer side. -/
theorem SeedRetainedPair.exists_first_terminalRegionalData {S : SelectedTailData}
    {K₀ : SeedCentralCutoff} {headLength length : ℝ}
    (P : SeedRetainedPair S K₀ headLength length)
    (hS : IsSelectedTail S)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hcone : ∀ side, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ uIcc (S.cut side S.chain.index)
      (S.joinInner side S.chain.index), (S.family S.sigma).w =ᶠ[𝓝 x] (fun t => c * t))
    (hhead : 0 < headLength) (B : FixedCentralBorder)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K₀.left) (hright : Γ.centralRight = exp K₀.right)
    {T B₀ C K : ℝ} (hT : selectedFirstInnerModelWindow ≤ T) (hC : 0 < C)
    (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hcolumn : referenceColumn Γ.reference = fixedCentralColumn B.chi)
    (f : R07FirstFrequency S.chain S.Cstar) (q : ℕ) (hq : 1 ≤ q) (hfq : f.1 = 2 * q)
    (hB : BufferHypotheses (B.modelBuffer q T B₀))
    (model : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (hk : ∀ i, 0 < fixedCentralModelCutEnergy model i)
    (herror : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa model) (fun _ => 1)
        (model.physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
        (1 : ℝ) / 8)
    {Kfirst η ε H : ℝ}
    (hcost : sqrt 2 * fixedCentralFirstInverseCost model (2 * (q : ℝ)) T B₀ ≤ Kfirst)
    (hη : 0 < η) (hε : 0 ≤ ε) (hH : 2 * log 2 < H) (hL : H < length)
    (hbudget : ε + Kfirst * ε ^ 2 ≤ η / 16)
    (hsource : terminalConeSourceConstant * exp (-((f.1 : ℝ) * H / 2)) ≤
      sqrt (1 / (f.1 : ℝ)) * ε)
    (henergy : (1 / (f.1 : ℝ)) * (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) *
      exp (-((f.1 : ℝ) * H)) ≤ (1 / (f.1 : ℝ)) * ε)
    (v : Bool → ℝ → ℝ)
    (hv : ∀ side, SelectedFirstNaturalData S side f.1 (v side) ∧
      2 * η ≤ selectedFirstBoundaryMargin S side f.1 (v side))
    (hincoming : ∀ side, ContDiff ℝ ∞ (S.incoming side f.1))
    (houter : SelectedTerminalOuterSupply (P.firstTerminalMatching Γ.reference f.1 η v)) :
    ∃ W : TerminalRegionalData Γ.reference,
      W.matching.frequency = f.1 ∧ W.matching.transitionIndex = S.chain.index ∧
      W.matching.margin = η ∧ W.inverseCost = Kfirst ∧
      W.sourceCost = ε ∧ W.energyCost = ε ∧
      W.matching.innerLeft = P.sideRadius false * S.joinInner false S.chain.index ∧
      W.matching.innerRight = P.sideRadius true * S.joinInner true S.chain.index ∧
      ∀ i, W.attenuation i = 0 := by
  classical
  let D := Γ.reference
  let cut := fun side => P.sideRadius side * S.joinInner side S.chain.index
  let V := fun side => radialRadiusScale (P.sideRadius side) 1 (v side)
  let boundary := fun side => outerUnitState
    (selectedBoundaryState D f.1 (r07OutwardSign side) (cut side) (V side))
  let base := P.firstTerminalMatching D f.1 η v
  have hD : RadialProfileGeometry D := (Classical.choose_spec hΓ.2.1).1
  have hdata (side : Bool) := P.selected_first_fixed_natural_data hD hw hS side f
    (hv side).1 (hv side).2
  obtain ⟨A, u, hnorm, _, hsolve, hunique, hrepresentative⟩ :=
    P.exists_first_inner_inverse hS hfirst hcone hhead B hΓ hw hleft hright hT hC
      hTL hTR hmodel hcolumn q hq hB model hk herror base hfq rfl rfl rfl
  obtain ⟨R, rep, Q, p, houterRealized⟩ := houter A u
  let M : RadialMatchingData D :=
    { base with
      innerInverse := A
      innerRepresentative := u
      outerInverse := R
      outerRepresentative := rep
      outerPoisson := Q
      outerFunction := p }
  let U (side : Bool) : SeedPhysicalFirstIncoming P D side f.1 :=
    Classical.choice (P.exists_physical_firstIncoming hw hS side f.2.1 f.2.2.1 f.2.2.2
      (hincoming side) (hcone side))
  let χ := fun i => P.firstTerminalCutoff H (selectedTerminalSide i)
  let standIn := fun i => (U (selectedTerminalSide i)).solution
  have hlog : log 2 < H := by linarith [log_pos (by norm_num : (1 : ℝ) < 2)]
  obtain ⟨hχ, hderiv, hdisjoint, hcolumnDisjoint, hχgerm, hODE⟩ :=
    P.first_cutoff_geometry hS hfirst hhead hΓ hleft hright hlog hL U
  have hbounds := P.first_terminal_cutoff_estimates hΓ hw hS hfirst hhead hleft hright
    hcone f.2.1 U hH hL hε hsource henergy
  obtain ⟨hLC, hCI, hIL, hLR, hRI, hIC, hCJ⟩ :=
    P.first_matching_order hS hfirst hhead hleft hright
  have hcutL : cut false < Γ.centralLeft := hLC.trans (hCI.trans hIL)
  have hcutR : Γ.centralRight < cut true := hRI.trans (hIC.trans hCJ)
  have hcut (i : Fin 2) : matchingCut D M i = cut (selectedTerminalSide i) :=
    selectedTerminalMatching_cut D f.1 S.chain.index η cut (fun _ => 1 / (f.1 : ℝ)) boundary i
  have hdiag (i : Fin 2) : M.A i i = (boundary (selectedTerminalSide i)).1 ∧
      M.B i i = (boundary (selectedTerminalSide i)).2 :=
    selectedTerminalMatching_diagonal D f.1 S.chain.index η cut
      (fun _ => 1 / (f.1 : ℝ)) boundary i
  have hj : (2 : ℝ) ≤ f.1 := by exact_mod_cast f.2.1
  have hjpos : (0 : ℝ) < f.1 := (by norm_num : (0 : ℝ) < 2).trans_le hj
  have hhalf : 1 / (f.1 : ℝ) ≤ 1 / 2 :=
    (div_le_div_iff₀ hjpos (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hj)
  let W : TerminalRegionalData D := {
    matching := M
    cut_order := ⟨(hdata false).1.1, hcutL.trans (hLR.trans hcutR), (hdata true).1.2⟩
    column_inside := by
      intro r hr
      have hs := connectedReference_column_in_central hΓ (subset_tsupport _ hr)
      exact ⟨hcutL.trans hs.1, hs.2.trans hcutR⟩
    margin_pos := hη
    diagonal := by
      intro i
      obtain ⟨_, _, _, _, hscale, _, _, hmargin⟩ := hdata (selectedTerminalSide i)
      refine ⟨hscale, one_div_pos.mpr hjpos, hhalf, ?_⟩
      change η ≤ |M.A i i * (1 / (f.1 : ℝ)) - M.B i i|
      rw [(hdiag i).1, (hdiag i).2]
      calc
        η ≤ 2 * η := by linarith only [hη]
        _ ≤ |(boundary (selectedTerminalSide i)).1 / (f.1 : ℝ) -
            (boundary (selectedTerminalSide i)).2| := hmargin
        _ = _ := by simp only [div_eq_mul_inv, one_mul]
    boundary_off_diagonal := selectedTerminalMatching_offDiagonal D f.1 S.chain.index η cut
      (fun _ => 1 / (f.1 : ℝ)) boundary
    boundary_normalized := by
      intro i
      rw [(hdiag i).1, (hdiag i).2]
      exact (hdata (selectedTerminalSide i)).2.2.2.2.2.2.1
    inner_solve := hsolve
    inner_unique := hunique
    inner_source := fun _ => rfl
    inner_representative := hrepresentative
    outer := houterRealized
    cutoff := χ
    standIn := standIn
    cutoff_smooth := fun i => hχ (selectedTerminalSide i)
    standIn_smooth := fun i => (U (selectedTerminalSide i)).smooth
    standIn_equation := fun i => hODE (selectedTerminalSide i)
    source_memLp := fun i => (hbounds (selectedTerminalSide i)).1
    cutoff_derivative_inside := fun i => hderiv (selectedTerminalSide i)
    cutoff_disjoint := by
      intro i k hik
      fin_cases i <;> fin_cases k
      · exact (hik rfl).elim
      · exact hdisjoint
      · exact hdisjoint.symm
      · exact (hik rfl).elim
    cutoff_column_disjoint := fun i => hcolumnDisjoint (selectedTerminalSide i)
    cutoff_boundary := by
      intro i
      rw [hcut]
      exact hχgerm (selectedTerminalSide i)
    standIn_boundary := by
      intro i
      rw [hcut]
      exact (U (selectedTerminalSide i)).join_value
    boundary_scale := by
      intro i
      rw [hcut]
    frequency_pos := hjpos
    boundary_slope := by
      intro i
      change standInBoundarySlope (bufferSign i) ((f.1 : ℝ) ^ 2)
        (matchingCut D M i) (U (selectedTerminalSide i)).solution = 1 / (f.1 : ℝ)
      rw [hcut, selectedTerminalSide_sign]
      exact (U (selectedTerminalSide i)).join_slope
    attenuation := fun _ => 0
    sourceCost := ε
    energyCost := ε
    inverseCost := Kfirst
    sourceCost_nonneg := hε
    energyCost_nonneg := hε
    source_bound := by
      intro i
      simpa only [neg_zero, exp_zero, mul_one] using (hbounds (selectedTerminalSide i)).2.1
    energy_bound := by
      intro i
      simpa only [mul_zero, neg_zero, exp_zero, mul_one] using
        (hbounds (selectedTerminalSide i)).2.2
    inverse_bound := hnorm.trans hcost
    error_budget := by
      intro i k
      simpa only [neg_zero, sub_zero, exp_zero, mul_one] using hbudget }
  exact ⟨W, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

end ContinuousFlexibility.Radial
