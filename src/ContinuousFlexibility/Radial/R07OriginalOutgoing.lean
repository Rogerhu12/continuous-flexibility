import ContinuousFlexibility.Radial.R07OriginalFamily
import ContinuousFlexibility.Radial.R07DeepTailPhysical
import ContinuousFlexibility.Radial.R07DeepTailEntry
import ContinuousFlexibility.Radial.R07DensityParameter
import ContinuousFlexibility.Radial.R07OutgoingInvariance
import ContinuousFlexibility.Radial.R07TailEquationScale

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem exists_r07OriginalOutgoing {T : MorseChainData} (hR06 : R06Statement)
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ) (C : ℕ → ℝ)
    (hfamily : ∀ σ, (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) →
      MorseChainRealization T σ (morseChainReferenceFamily G phi σ) C ∧
        MorseMassResistanceBounds T σ (morseChainReferenceFamily G phi σ) C)
    (side : Bool) (k j : ℕ) (hj : 2 ≤ j) :
    let e := r07CellEntry T side (T.index + k)
    ∃ V : HeightRatios → ℝ → ℝ,
      (∀ σ, ContDiff ℝ ∞ (V σ) ∧
        RadialNaturalTail (morseChainReferenceFamily G phi σ.val) side j e (V σ)) ∧
      Continuous (fun σ => r07OutgoingState j e (V σ)) ∧
      (∀ σ, r07OutgoingState j e (V σ) ≠ (0, 0)) ∧
      ∀ σ t, r07OutgoingState j e (V (r07HeightUpdate σ (T.index + k) t)) =
        r07OutgoingState j e (V σ) := by
  obtain ⟨A, η, K, hA, hη, hη1, hK, hoperator, hphysical, hparameter⟩ := hR06
  let D : HeightRatios → ReferenceData := fun σ => morseChainReferenceFamily G phi σ.val
  let base : HeightRatios := ⟨morseUnitHeights, morseUnitHeights_admissible⟩
  let e : ℝ := r07CellEntry T side (T.index + k)
  have hends (σ τ : ℕ → ℝ) :
      (morseChainReferenceFamily G phi σ).a = (morseChainReferenceFamily G phi τ).a ∧
        (morseChainReferenceFamily G phi σ).b = (morseChainReferenceFamily G phi τ).b := ⟨rfl, rfl⟩
  obtain ⟨start, hmin, hstart, h32, hall⟩ := r07_exists_uniform_deepTailPhysical T C
    (morseChainReferenceFamily G phi) hfamily hends hj hη hη1 hK (T.index + k + 2)
  let Q : HeightRatios → DeepTailData := fun σ => r07DeepTailData T (D σ) side j start η K
  let f : ℝ := if side then r07MassNodeRadius T side start else morseChainResistanceEnd T side start
  let tail : Set ℝ := if side then Ico e G.rightEnd else Ioc 1 e
  have hreal (σ : HeightRatios) : MorseChainRealization T σ.val (D σ) C :=
    (hfamily σ.val σ.property).1
  have hgeo (σ : HeightRatios) : RadialProfileGeometry (D σ) := r07_realization_geometry (hreal σ)
  have hacc (σ : HeightRatios) : IsAccumulatingProfile (D σ) := r07_realization_accumulating (hreal σ)
  have hFull (σ : HeightRatios) : DeepTailHypotheses (Q σ) ∧
      TailPhysicalRelation (D σ) (Q σ) side j start := hall σ.val σ.property side
  have hfixed (σ τ : HeightRatios) :
      (Q σ).entrance = (Q τ).entrance ∧ (Q σ).endpoint = (Q τ).endpoint ∧
      (Q σ).node = (Q τ).node ∧ (Q σ).Λ = (Q τ).Λ ∧ (Q σ).η = (Q τ).η ∧ (Q σ).K = (Q τ).K :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have he (σ : HeightRatios) : e ∈ radialCore (D σ) := by
    have hc := r07_chain_mass_cuts_core (hreal σ) side (Nat.le_add_right T.index k)
    cases side
    · exact hc.2.2
    · exact hc.1
  have hf (σ : HeightRatios) : f ∈ radialCore (D σ) :=
    r07_deepPhysicalEntrance_core (hreal σ) side hstart
  have hef : if side then e < f else f < e :=
    r07_deepPhysicalEntrance_after_entry G (hreal base) side (Nat.le_add_right T.index k) hmin
  have hfp : 0 < f := (hgeo base).1.trans (hf base).1
  have hentrance (σ : HeightRatios) : tailPhysicalRadius side (Q σ).entrance = f :=
    r07_radius_outwardLog side hfp
  have hwEq (σ : HeightRatios) : (D σ).w = morseChainGluedProfile G σ.val σ.property := by
    exact congrArg (fun R : ReferenceData => R.w)
      (morseChainReferenceFamily_admissible G phi σ.val σ.property)
  have hprofileJets (n : ℕ) : ContinuousOn
      (fun z : HeightRatios × ℝ => iteratedDeriv n (D z.1).w z.2) {z | z.2 ∈ tail} := by
    have h := continuousOn_morseChainGluedProfile_iteratedDeriv_tail G side k n
    cases side <;> simpa only [hwEq, tail, e, r07CellEntry, morseChainCellLeftRadius,
      morseChainCellRightRadius, Bool.false_eq_true, ite_false, ite_true] using h
  have hmap : MapsTo (tailPhysicalRadius side) (Ico (Q base).entrance (Q base).endpoint) tail := by
    intro x hx
    have hcore := r07_physical_radius_core_of_Ico (hgeo base)
      (r07_deepTail_entrance_core (hreal base) side j hstart η K) hx
    cases side
    · have hm : tailPhysicalRadius false x ≤ tailPhysicalRadius false (Q base).entrance :=
        exp_le_exp.mpr (neg_le_neg hx.1)
      rw [hentrance base] at hm
      exact ⟨hcore.1, hm.trans hef.le⟩
    · have hm : tailPhysicalRadius true (Q base).entrance ≤ tailPhysicalRadius true x :=
        exp_le_exp.mpr hx.1
      rw [hentrance base] at hm
      exact ⟨hef.le.trans hm, hcore.2⟩
  have hEndpoint : 0 < (if side then (D base).b else (D base).a) := by
    cases side
    · exact (hgeo base).1
    · exact (hgeo base).1.trans (hgeo base).2.1
  have hjets (n : ℕ) : ContinuousOn (fun z : HeightRatios × ℝ => radialJet n (Q z.1).p z.2)
      {z | z.2 ∈ Ico (Q z.1).entrance (Q z.1).endpoint} := by
    have h := continuousOn_r07PhysicalDensity_radialJet (D := D) side j hEndpoint
      (fun _ => rfl) (fun σ => (hgeo σ).2.2.1.1) hprofileJets hmap n
    exact h
  have hspan : uIcc f e ⊆ tail := by
    intro r hr
    cases side
    · rw [uIcc_of_le hef.le] at hr
      exact ⟨(hf base).1.trans_le hr.1, hr.2⟩
    · rw [uIcc_of_ge hef.le] at hr
      exact ⟨hr.1, hr.2.trans_lt (hf base).2⟩
  have hspanSet : {z : HeightRatios × ℝ | z.2 ∈ uIcc f e} ⊆
      {z : HeightRatios × ℝ | z.2 ∈ tail} := by
    intro z hz
    exact hspan hz
  have hw₀ : ContinuousOn (fun z : HeightRatios × ℝ => (D z.1).w z.2) {z | z.2 ∈ uIcc f e} := by
    simpa only [iteratedDeriv_zero] using (hprofileJets 0).mono hspanSet
  have hw₁ : ContinuousOn (fun z : HeightRatios × ℝ => deriv (D z.1).w z.2)
      {z | z.2 ∈ uIcc f e} := by
    simpa only [iteratedDeriv_one] using (hprofileJets 1).mono hspanSet
  have hline (σ : HeightRatios) : TailNaturalLineAndKernel (Q σ) := by
    rcases hoperator (Q σ) (hFull σ).1 le_rfl le_rfl with ⟨_, _, L, _, _, _, _, hL, _⟩
    exact hL
  have hflat (σ : HeightRatios) : TailPhysicalFlatConclusion (D σ) (Q σ) side j start :=
    (hphysical (D σ) (Q σ) side j start (hacc σ) (hFull σ).1 le_rfl le_rfl (hFull σ).2).1
  obtain ⟨U, V, hU, hV, hBcont, hBne⟩ := exists_continuous_radialNaturalFamily_of_R06_data D Q side j start hj
    hparameter (fun σ => ⟨(hFull σ).1, le_rfl, le_rfl⟩) hfixed hjets hacc
    (fun _ _ => ⟨rfl, rfl⟩) hline hflat (fun σ => (hFull σ).2) hentrance he hf hef hw₀ hw₁
  refine ⟨V, fun σ => ⟨(hV σ).1, (hV σ).2.1⟩, hBcont, hBne, ?_⟩
  intro σ t
  let τ : HeightRatios := r07HeightUpdate σ (T.index + k) t
  let scale : ℝ := t.val / σ.val (T.index + k)
  have hs : 0 < scale := div_pos (zero_lt_one.trans_le t.property.1)
    (zero_lt_one.trans_le (σ.property (T.index + k)).1)
  have hscale (r : ℝ) (hr : r ∈ tail) : (D τ).w =ᶠ[𝓝 r] fun x => scale * (D σ).w x := by
    rw [hwEq τ, hwEq σ]
    apply morseChainGluedProfile_update_tail_germ G σ.val σ.property (Nat.le_add_right T.index k)
      t.property side
    cases side <;> simpa only [tail, e, r07CellEntry, morseChainCellLeftRadius,
      morseChainCellRightRadius, Bool.false_eq_true, ite_false, ite_true,
      Nat.add_sub_cancel_left] using hr
  have hp : EqOn (Q τ).p (fun x => scale * (Q σ).p x)
      (Ioo (Q σ).entrance (Q σ).endpoint) := by
    intro x hx
    have hx' : x ∈ Ico (Q base).entrance (Q base).endpoint := ⟨hx.1.le, hx.2⟩
    have hw := (hscale (tailPhysicalRadius side x) (hmap hx')).eq_of_nhds
    have hEnd : (if side then (D τ).b else (D τ).a) =
        (if side then (D σ).b else (D σ).a) := rfl
    change r07PhysicalDensity (D τ) side j x = scale * r07PhysicalDensity (D σ) side j x
    simp only [r07PhysicalDensity, hEnd, hw]
    ring
  have hUder := tailNatural_normalized_deriv_scale
    (hfixed τ σ).1 (hfixed τ σ).2.1 (hfixed τ σ).2.2.2.1 hs hp
    (hFull σ).1.1 (hline σ) (hU σ).1 (hU σ).2 (hU τ).1 (hU τ).2
  apply r07OutgoingState_eq_of_scaled_profile (hgeo σ) (hgeo τ)
    (he σ) (hf σ) (he τ) (hf τ) hef hs
    (fun r hr => hscale r (hspan (by simpa only [uIcc_comm e f] using hr)))
    (hV σ).1 (hV τ).1 (hV σ).2.1 (hV τ).2.1
  · exact ((hV τ).2.2.1).trans ((hV σ).2.2.1).symm
  · have hEnd : (if side then (D τ).b else (D τ).a) =
        (if side then (D σ).b else (D σ).a) := rfl
    have hSlopeEq :
        r07PhysicalInitialSlope (if side then (D τ).b else (D τ).a) side j
            (Q τ).entrance (deriv (U τ) (Q τ).entrance) =
          r07PhysicalInitialSlope (if side then (D σ).b else (D σ).a) side j
            (Q σ).entrance (deriv (U σ) (Q σ).entrance) := by
      simpa only [hEnd, (hfixed τ σ).1] using congrArg
        (fun z : ℝ => r07PhysicalInitialSlope (if side then (D σ).b else (D σ).a)
          side j (Q σ).entrance z) hUder
    exact ((hV τ).2.2.2).trans (hSlopeEq.trans ((hV σ).2.2.2).symm)

/-- Total raw-sequence form of the actual outgoing family, with its state
defined directly from that same physical solution. -/
theorem exists_r07OriginalOutgoing_raw {T : MorseChainData} (hR06 : R06Statement)
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ) (C : ℕ → ℝ)
    (hfamily : ∀ σ, (∀ i, 1 ≤ σ i ∧ σ i ≤ 2) →
      MorseChainRealization T σ (morseChainReferenceFamily G phi σ) C ∧
        MorseMassResistanceBounds T σ (morseChainReferenceFamily G phi σ) C)
    (side : Bool) (k j : ℕ) (hj : 2 ≤ j) :
    let e := r07CellEntry T side (T.index + k)
    ∃ V : (ℕ → ℝ) → ℝ → ℝ,
      (∀ σ ∈ heightCube, ContDiff ℝ ∞ (V σ) ∧
        RadialNaturalTail (morseChainReferenceFamily G phi σ) side j e (V σ)) ∧
      ContinuousOn (fun σ => r07OutgoingState j e (V σ)) heightCube ∧
      (∀ σ ∈ heightCube, r07OutgoingState j e (V σ) ≠ (0, 0)) ∧
      ∀ σ ∈ heightCube, ∀ t ∈ Icc (1 : ℝ) 2,
        r07OutgoingState j e (V (Function.update σ (T.index + k) t)) =
          r07OutgoingState j e (V σ) := by
  obtain ⟨V, hV, hBc, hBne, hBi⟩ := exists_r07OriginalOutgoing hR06 G phi C hfamily side k j hj
  let e : ℝ := r07CellEntry T side (T.index + k)
  let Vraw : (ℕ → ℝ) → ℝ → ℝ := r07HeightExtension (fun _ => 0) V
  let B : HeightRatios → ℝ × ℝ := fun σ => r07OutgoingState j e (V σ)
  have hstate (σ : ℕ → ℝ) (hσ : σ ∈ heightCube) :
      r07OutgoingState j e (Vraw σ) = B ⟨σ, mem_heightCube.mp hσ⟩ := by
    rw [show Vraw σ = V ⟨σ, mem_heightCube.mp hσ⟩ from
      r07HeightExtension_admissible (fun _ => 0) V σ (mem_heightCube.mp hσ)]
  refine ⟨Vraw, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    rw [show Vraw σ = V ⟨σ, mem_heightCube.mp hσ⟩ from
      r07HeightExtension_admissible (fun _ => 0) V σ (mem_heightCube.mp hσ)]
    exact hV ⟨σ, mem_heightCube.mp hσ⟩
  · refine (continuousOn_r07HeightExtension (1, 0) hBc).congr ?_
    intro σ hσ
    change r07OutgoingState j e (Vraw σ) = r07HeightExtension (1, 0) B σ
    rw [hstate σ hσ, r07HeightExtension_admissible (1, 0) B σ (mem_heightCube.mp hσ)]
  · intro σ hσ
    rw [hstate σ hσ]
    exact hBne ⟨σ, mem_heightCube.mp hσ⟩
  · intro σ hσ t ht
    have hτ := update_mem_heightCube hσ (T.index + k) ht
    rw [hstate _ hτ, hstate σ hσ]
    exact hBi ⟨σ, mem_heightCube.mp hσ⟩ ⟨t, ht⟩

end ContinuousFlexibility.Radial
