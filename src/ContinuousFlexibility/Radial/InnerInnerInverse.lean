import ContinuousFlexibility.Radial.InnerSelectedInnerInverse
import ContinuousFlexibility.Radial.PositiveBufferR09

/-!
# Lemma 6.3: the inner inverse with the original order of choices

The proved positive-buffer compression theorem supplies every local
model. The weight exponent is fixed first, then the frequency threshold,
then an index floor that permits every later first index. Only afterwards
are the central cuts and cone lengths chosen.

For every raw physical realization with these same selected parameters,
one constant controls all bands and all positive even modes. The inverse
is chosen before the weight exponent gamma and satisfies both inverse
identities, the exact Schur formula, and both weighted estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- Reindex the same family at the actual selected data. This changes
no witness; proof irrelevance preserves the original selected models. -/
theorem innerMorsePhysicalFamily_at_selected
    {a Cstar CM KM η : ℝ} {N : ℕ}
    (hfamily : InnerMorsePhysicalFamily a Cstar N CM KM η)
    (S : SelectedTailData) (hCstar : S.Cstar = Cstar) (hindex : S.chain.index = N) :
    InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η := by
  simpa only [hCstar, hindex] using hfamily

/-- The inner inverse lemma, with all analytic inputs derived from the
proved R09 theorem. The remaining quantified geometry consists only
of the actual selected profile, charts, cuts, and positive connectors.

The fixed localized loss in InnerSelectedInverseStatement is 37. Its
single inverse precedes every allowed gamma and both weight signs. -/
theorem inner_inverse {a : ℝ} (ha : 0 ≤ a) :
    ∃ CM KM CC KC Cstar : ℝ,
      0 < CM ∧ 0 < KM ∧ 0 < CC ∧ 0 < KC ∧ 0 < Cstar ∧
      innerMorseBufferThreshold ≤ Cstar ∧
      ∀ initial : ℕ, ∃ Nfloor : ℕ,
        initial ≤ Nfloor ∧ 4096 ≤ Nfloor ∧ 64 * a ≤ (Nfloor : ℝ) ∧
        ∀ N : ℕ, Nfloor ≤ N → ∀ centralFloor : ℝ, ∃ X₀ : ℝ,
          centralFloor ≤ X₀ ∧
          ∃ hX : 8 ≤ X₀, ∃ hsupport : innerCentralModelBorderRadius < X₀,
          ∃ hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ (1 / 16),
          ∀ coneFloor Acone bcone dcone ccone : ℝ,
            0 ≤ bcone → 0 ≤ dcone → 0 < ccone → ∃ L : ℝ,
              1 ≤ L ∧ coneFloor ≤ L ∧
              ∃ hMorseFamily : InnerMorsePhysicalFamily a Cstar N CM KM (1 / 16),
                InnerConeHeadSmall Acone bcone dcone ccone (1 / 16) L ∧
                ∀ (S : SelectedTailData) (D : ReferenceData)
                  (P : InnerSelectedPhysicalGeometry S D X₀)
                  (hCstar : S.Cstar = Cstar) (hindex : S.chain.index = N),
                  ∃ C : ℝ, 0 < C ∧ InnerSelectedInverseStatement P hCentralFamily
                    (innerMorsePhysicalFamily_at_selected hMorseFamily S hCstar hindex)
                    hX hsupport C := by
  obtain ⟨CM, KM, CC, KC, hCM, hKM, hCC, hKC, Cstar, hCstar, hthreshold, hchoices⟩ :=
    exists_innerPhysicalOrderedChoices r09Statement ha
  refine ⟨CM, KM, CC, KC, Cstar, hCM, hKM, hCC, hKC, hCstar, hthreshold, ?_⟩
  intro initial
  obtain ⟨Nfloor, hinitial, hlarge, hweight, hindices⟩ :=
    hchoices (1 / 16) (by norm_num) initial
  refine ⟨Nfloor, hinitial, hlarge, hweight, ?_⟩
  intro N hNfloor centralFloor
  obtain ⟨X₀, hcentralFloor, hX, hsupport, hCentralFamily, hheads⟩ :=
    hindices N hNfloor centralFloor
  refine ⟨X₀, hcentralFloor, hX, hsupport, hCentralFamily, ?_⟩
  intro coneFloor Acone bcone dcone ccone hbcone hdcone hccone
  obtain ⟨L, hL, hconeFloor, hMorseFamily, hcone⟩ :=
    hheads coneFloor Acone bcone dcone ccone hbcone hdcone hccone
  refine ⟨L, hL, hconeFloor, hMorseFamily, hcone, ?_⟩
  intro S D P hSCstar hSindex
  have hN : 4096 ≤ S.chain.index := by
    rw [hSindex]
    exact hlarge.trans hNfloor
  have hNa : 64 * a ≤ (S.chain.index : ℝ) := by
    rw [hSindex]
    exact hweight.trans (by exact_mod_cast hNfloor)
  exact P.exists_innerInverseStatement hCentralFamily
    (innerMorsePhysicalFamily_at_selected hMorseFamily S hSCstar hSindex)
    hX hsupport ha hN hNa hCC.le hCM (by norm_num) (by norm_num)

/-- info: 'ContinuousFlexibility.Radial.inner_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inner_inverse

end ContinuousFlexibility.Radial
