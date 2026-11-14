module

public import ContinuousFlexibility.Radial.SelectedFirstMargin
public import ContinuousFlexibility.Radial.SelectedFirstNaturalTransport
public import ContinuousFlexibility.Radial.FirstConePhysicalIncoming
public import ContinuousFlexibility.Radial.FirstConeLayerSeparation
public import ContinuousFlexibility.Radial.SelectedOuterPoisson

/-!
# The fixed first-band natural family on any retained reference

The natural family and its finite positive margin are inputs chosen on
the original selected tail. The retained pair, cone length and connected
reference are later inputs. Only the incoming solution is normalized on
that final geometry; the natural solution is exactly the radius dilation
of the already chosen member of the family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

/-- Transport a fixed natural representative and its original margin,
without choosing another continuation after the retained pair is known. -/
theorem SeedRetainedPair.selected_first_fixed_natural_data {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hD : RadialProfileGeometry D) (hw : D.w = P.pair.profile)
    (hS : IsSelectedTail S) (right : Bool) (f : R07FirstFrequency S.chain S.Cstar)
    {v : ℝ → ℝ} {η : ℝ} (hv : SelectedFirstNaturalData S right f.1 v)
    (hmargin : 2 * η ≤ selectedFirstBoundaryMargin S right f.1 v) :
    let c := P.sideRadius right * S.joinInner right S.chain.index
    let V := radialRadiusScale (P.sideRadius right) 1 v
    let state := selectedBoundaryState D f.1 (r07OutwardSign right) c V
    let AB := outerUnitState state
    c ∈ radialCore D ∧ ContDiff ℝ ∞ V ∧ RadialNaturalTail D right f.1 c V ∧
      state = selectedBoundaryState (S.family S.sigma) f.1 (r07OutwardSign right)
        (S.joinInner right S.chain.index) v ∧
      0 < standInBoundaryScale ((f.1 : ℝ) ^ 2) (D.w c) c ∧ state ≠ 0 ∧
      AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧ 2 * η ≤ |AB.1 / (f.1 : ℝ) - AB.2| := by
  have hD₀ : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  obtain ⟨_, _, hp, hwp, horder, _, _, _, _, _, _, _, _⟩ :=
    hS.2.2.2.2.2 right S.chain.index f.1 f.2.1 f.2.2.1 f.2.2.2
  have hout : if right then S.cut right S.chain.index ≤ S.joinInner right S.chain.index
      else S.joinInner right S.chain.index ≤ S.cut right S.chain.index := by
    cases right
    · exact horder.2.le
    · exact horder.1.le
  obtain ⟨hc, hprofile, hN⟩ :=
    P.reference_natural_tail_transport hD hw hS right hp hout hv.2.1
  have hV := contDiff_radialRadiusScale hv.1 (P.sideRadius right) 1
  have hj : (f.1 : ℝ) ≠ 0 := by
    exact_mod_cast (show f.1 ≠ 0 from by have := f.2.1; omega)
  have hε : r07OutwardSign right ≠ 0 := by
    cases right <;> norm_num [r07OutwardSign]
  have hstate := selectedBoundaryState_radiusScale_one
    (D := S.family S.sigma) (E := D) (ε := r07OutwardSign right)
    (P.sideRadius_pos right).ne' (P.sideHeight_pos right).ne'
    hj (hD₀.1.trans hp.1).ne' hwp.ne' hprofile v
  have hne := selectedBoundaryState_ne_zero_of_natural hD hj hc hε hV hN
  refine ⟨hc, hV, hN, hstate,
    standInBoundaryScale_pos (sq_pos_of_ne_zero hj) (hD.2.2.2.2.1 _ hc)
      (hD.1.trans hc.1), hne, outerUnitState_unit hne, ?_⟩
  rw [hstate]
  exact hmargin

/-- Both first-band Poisson columns on the same actual reference. The
family `v` and margin `η` precede all inputs describing that reference.
The returned incoming records retain their actual equation and cone germ,
so their slope is the slope of those solutions, exactly `1 / j`. -/
theorem selected_first_outerPoisson_data {S : SelectedTailData}
    (v : Bool → R07FirstFrequency S.chain S.Cstar → ℝ → ℝ) {η : ℝ}
    (hv : ∀ right f, SelectedFirstNaturalData S right f.1 (v right f) ∧
      2 * η ≤ selectedFirstBoundaryMargin S right f.1 (v right f))
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes) (hselected : Γ.selected = S)
    (hq : 0 < q) (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (htwo : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hincoming : ∀ (right : Bool) (f : R07FirstFrequency S.chain S.Cstar),
      ContDiff ℝ ∞ (S.incoming right f.1))
    (hcone : ∀ right, ∃ C : ℝ, 0 < C ∧ ∀ r ∈ uIcc (S.cut right S.chain.index)
        (S.joinInner right S.chain.index),
      (S.family S.sigma).w =ᶠ[nhds r] fun t => C * t)
    (f : R07FirstFrequency S.chain S.Cstar) :
    let D := Γ.reference
    let cut := fun right => P.sideRadius right * S.joinInner right S.chain.index
    let V := fun right => radialRadiusScale (P.sideRadius right) 1 (v right f)
    let lam := fun right => standInBoundaryScale ((f.1 : ℝ) ^ 2) (D.w (cut right)) (cut right)
    ∃ U : ∀ right, SeedPhysicalFirstIncoming P D right f.1,
      D.a < cut false ∧ cut false < Γ.centralLeft ∧
      Γ.centralRight < cut true ∧ cut true < D.b ∧ cut false < cut true ∧
      (∀ right,
        ContDiff ℝ ∞ (V right) ∧ RadialNaturalTail D right f.1 (cut right) (V right) ∧
        selectedBoundaryState D f.1 (r07OutwardSign right) (cut right) (V right) =
          selectedBoundaryState (S.family S.sigma) f.1 (r07OutwardSign right)
            (S.joinInner right S.chain.index) (v right f) ∧
        0 < lam right ∧
        selectedBoundaryState D f.1 (r07OutwardSign right) (cut right) (V right) ≠ 0 ∧
        let d := standInBoundarySlope (r07OutwardSign right) ((f.1 : ℝ) ^ 2)
          (cut right) (U right).solution
        let AB := outerUnitState
          (selectedBoundaryState D f.1 (r07OutwardSign right) (cut right) (V right))
        d = 1 / (f.1 : ℝ) ∧ 0 < d ∧ d ≤ 1 / 2 ∧
          AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧ 2 * η ≤ |AB.1 * d - AB.2|) ∧
      ∀ M : RadialMatchingData D, M.frequency = f.1 →
        M.innerLeft = cut false → M.innerRight = cut true →
        (∀ i, M.boundaryScale i = lam (if i = 0 then false else true)) →
        ∃ Q : Fin 2 → RadialModePair D, ∃ p : Fin 2 → ℝ → ℝ,
          ∀ i,
            let right := if i = 0 then false else true
            let state := selectedBoundaryState D f.1 (bufferSign i) (cut right) (V right)
            let AB := outerUnitState state
            p i = modeOuterSideFunction M.innerLeft M.innerRight right
              (fun r => V right r / (sqrt (state.1 ^ 2 + state.2 ^ 2) * sqrt (lam right))) ∧
            (((Q i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p i) ∧
            (((Q i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
              (Ioo M.innerLeft M.innerRight)] fun _ => 0) ∧
            (∀ r ∈ Ioo M.innerLeft M.innerRight, p i r = 0) ∧
            ContDiffOn ℝ 2 (p i) (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
            (Q i).2 = 0 ∧ ModeLocalEquation D f.1 (matchingOuterRegion D M) (Q i) 0 ∧
            AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧
            ∀ k, p i (matchingCut D M k) = (if k = i then AB.1 else 0) /
                sqrt (M.boundaryScale k) ∧
              matchingOuterFlux D M (p i) k = (if k = i then AB.2 else 0) := by
  classical
  let D := Γ.reference
  let cut := fun right => P.sideRadius right * S.joinInner right S.chain.index
  let V := fun right => radialRadiusScale (P.sideRadius right) 1 (v right f)
  let lam := fun right => standInBoundaryScale ((f.1 : ℝ) ^ 2) (D.w (cut right)) (cut right)
  have hS : IsSelectedTail S := hselected ▸ hΓ.1
  have hD : RadialProfileGeometry D := by
    obtain ⟨C, hC⟩ := hΓ.2.1
    exact hC.1
  have hdata (right : Bool) := P.selected_first_fixed_natural_data hD hw hS right f
    (hv right f).1 (hv right f).2
  let U (right : Bool) : SeedPhysicalFirstIncoming P D right f.1 :=
    Classical.choice (P.exists_physical_firstIncoming hw hS right f.2.1 f.2.2.1
      f.2.2.2 (hincoming right f) (hcone right))
  have hd (right : Bool) : standInBoundarySlope (r07OutwardSign right) ((f.1 : ℝ) ^ 2)
      (cut right) (U right).solution = 1 / (f.1 : ℝ) := (U right).join_slope
  have hj : (2 : ℝ) ≤ f.1 := by exact_mod_cast f.2.1
  have hjpos : (0 : ℝ) < f.1 := lt_of_lt_of_le (by norm_num) hj
  have hhalf : 1 / (f.1 : ℝ) ≤ 1 / 2 :=
    (div_le_div_iff₀ hjpos (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hj)
  obtain ⟨hLC, hCI, hIL, hLH, hHR, hRC, hCJ⟩ :=
    P.first_matching_order hS htwo hq hleft hright
  have hL : cut false < Γ.centralLeft := hLC.trans (hCI.trans hIL)
  have hR : Γ.centralRight < cut true := hHR.trans (hRC.trans hCJ)
  have hLR : cut false < cut true := hL.trans (hLH.trans hR)
  have hV (right : Bool) : ContDiff ℝ ∞ (V right) := (hdata right).2.1
  have hN (right : Bool) : RadialNaturalTail D right f.1 (cut right) (V right) :=
    (hdata right).2.2.1
  have hlam (right : Bool) : 0 < lam right := (hdata right).2.2.2.2.1
  have hne (right : Bool) :
      selectedBoundaryState D f.1 (r07OutwardSign right) (cut right) (V right) ≠ 0 :=
    (hdata right).2.2.2.2.2.1
  refine ⟨U, (hdata false).1.1, hL, hR, (hdata true).1.2, hLR, ?_, ?_⟩
  · intro right
    obtain ⟨_, hVs, hNs, hstate, hscale, hstateNe, hunit, hmargin⟩ := hdata right
    refine ⟨hVs, hNs, hstate, hscale, hstateNe, hd right, ?_, ?_, hunit, ?_⟩
    · rw [hd]
      exact one_div_pos.mpr hjpos
    · rw [hd]
      exact hhalf
    · rw [hd]
      simpa only [D, one_div, div_eq_mul_inv, one_mul] using hmargin
  · intro M hfreq hcutL hcutR hscale
    have ha : D.a < M.innerLeft := by rw [hcutL]; exact (hdata false).1.1
    have hm : M.innerLeft < M.innerRight := by rw [hcutL, hcutR]; exact hLR
    have hb : M.innerRight < D.b := by rw [hcutR]; exact (hdata true).1.2
    have hcutM (i : Fin 2) : matchingCut Γ.reference M i =
        P.sideRadius (if i = 0 then false else true) *
          S.joinInner (if i = 0 then false else true) S.chain.index := by
      fin_cases i
      · exact hcutL
      · exact hcutR
    have hindex (i : Fin 2) :
        (if (if i = 0 then false else true) then (1 : Fin 2) else 0) = i := by
      fin_cases i <;> norm_num
    have hsign (i : Fin 2) : bufferSign i =
        r07OutwardSign (if i = 0 then false else true) := by
      fin_cases i <;> norm_num [bufferSign, r07OutwardSign]
    have hpoisson (i : Fin 2) := exists_selectedOuterPoisson hΓ.2.1 M ha hm hb
      (if i = 0 then false else true) (hV _)
      (by rw [hindex, hfreq, hcutM]; exact hN _)
      (by rw [hindex, hscale]; exact hlam _)
      (by rw [hindex, hscale, hfreq, hcutM])
      (by rw [hindex, hfreq, hcutM, hsign]; exact hne _)
    choose Q p hp using hpoisson
    refine ⟨Q, p, ?_⟩
    intro i
    simpa only [hindex, hfreq, hcutM, hscale] using hp i

end ContinuousFlexibility.Radial
