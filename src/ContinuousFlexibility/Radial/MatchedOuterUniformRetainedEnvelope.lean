module

public import ContinuousFlexibility.Radial.MatchedOuterLaterRetainedEnvelope

/-!
# A common actual outer envelope at every retained frequency

Only finitely many frequencies occur below the proved uniform transition
threshold. The actual fixed-frequency constructions handle these modes,
and their finite maximum is taken after the single retained geometry is
fixed. The whole operators and natural columns are kept unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem SeedRetainedPair.exists_uniform_selectedOuter_tailEnvelope
    {S : SelectedTailData} {K₀ : SeedCentralCutoff} {q length Cstar : ℝ} {requested : ℕ}
    (P : SeedRetainedPair S K₀ q length) (metadata : R10aSelectedMetadata Cstar requested S)
    (Γ : ConnectedReferenceGeometry)
    (hE : IsAccumulatingProfile Γ.reference) (hPE : RadialPartition Γ.reference)
    (hw : Γ.reference.w = P.pair.profile) (hcoordinates : R11aRetainedCoordinates P Γ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ n j : ℕ, 2 ≤ j → Even j → radialFrequencyBand S.chain S.Cstar n j →
        ∀ right : Bool, MatchedOuterTailEnvelope (S.family S.sigma) Γ.reference hPE right
          (P.sideRadius right * S.joinInner right n) j n C A := by
  classical
  obtain ⟨C₁, A₁, hC₁, hA₁, N₀, hN₀, htail⟩ :=
    P.exists_uniform_laterOuter_tailEnvelope metadata Γ hE hPE hw hcoordinates
  let J₀ := ⌈radialFrequencyThreshold S.chain S.Cstar N₀⌉₊
  let ι := {p : Fin N₀ × Fin J₀ //
    2 ≤ (p.2 : ℕ) ∧ Even (p.2 : ℕ) ∧
      radialFrequencyBand S.chain S.Cstar p.1 p.2}
  have hfixed (i : ι × Bool) :
      ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
        MatchedOuterTailEnvelope (S.family S.sigma) Γ.reference hPE i.2
          (P.sideRadius i.2 * S.joinInner i.2 i.1.val.1)
          i.1.val.2 i.1.val.1 B A :=
    P.exists_fixed_selectedOuter_tailEnvelope metadata Γ hE hPE hw hcoordinates
      i.1.property.1 i.1.property.2.1 i.1.property.2.2 i.2
  choose B A hB hA hfixed using hfixed
  obtain ⟨CB, hCB⟩ := (Set.finite_range B).bddAbove
  obtain ⟨CA, hCA⟩ := (Set.finite_range A).bddAbove
  let C := max C₁ (max 1 CB)
  let a := max A₁ (max 1 CA)
  have hC : 0 < C := hC₁.trans_le (le_max_left _ _)
  have ha : 0 < a := hA₁.trans_le (le_max_left _ _)
  refine ⟨C, a, hC, ha, ?_⟩
  intro n j hj heven hband right
  by_cases hn : N₀ ≤ n
  · exact (htail n hn j hj heven hband right).mono hC₁.le
      (le_max_left _ _) (le_max_left _ _)
  · have hnlt : n < N₀ := Nat.lt_of_not_ge hn
    have hS := metadata.selected
    have h := (hS.2.2.2.1 S.sigma hS.2.2.1).1
    have hthreshold : radialFrequencyThreshold S.chain S.Cstar n ≤
        radialFrequencyThreshold S.chain S.Cstar N₀ :=
      (morseTransition_threshold_strictMonoOn S.chain hS.1 h.d_eq).monotoneOn
        hband.1 ((Nat.le_add_right S.chain.index 3).trans hN₀) hnlt.le
    have hjlt : j < J₀ := Nat.lt_ceil.mpr (hband.2.2.trans_le hthreshold)
    let i : ι := ⟨(⟨n, hnlt⟩, ⟨j, hjlt⟩), hj, heven, hband⟩
    exact (hfixed (i, right)).mono (hB (i, right)).le
      (((hCB (mem_range_self (i, right))).trans (le_max_right _ _)).trans (le_max_right _ _))
      (((hCA (mem_range_self (i, right))).trans (le_max_right _ _)).trans (le_max_right _ _))

end ContinuousFlexibility.Radial
