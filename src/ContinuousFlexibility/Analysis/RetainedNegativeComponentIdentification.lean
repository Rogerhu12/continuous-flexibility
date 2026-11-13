import ContinuousFlexibility.Radial.R11aRetainedFamily
import ContinuousFlexibility.Radial.MorseNegativeCover
import ContinuousFlexibility.Radial.SeedCentralReturn

/-!
# Exact negative components of the same retained reference

The increasing connectors introduce no negative components. Each tail
component is identified with the displayed turning interval of an
actual retained Morse model, including the original model index and
the fact that its closed interval stays inside that tail. The central
case is the one fixed physical oscillator interval. The reference and
the retained pair are never replaced.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

private theorem scaled_morse_component_identification
    {Q : MorseChainData} {σ : ℕ → ℝ} {D E : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization Q σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {R H : ℝ} (hR : 0 < R) (hH : 0 < H)
    (hE : ContDiff ℝ ∞ E.w)
    (hcore : ∀ s ∈ radialTailInterval D side (morseChainSeam Q side Q.index),
      R * s ∈ radialCore E)
    (hprofile : ∀ s ∈ radialTailInterval D side (morseChainSeam Q side Q.index),
      E.w (R * s) = H * R * D.w s)
    {l h r : ℝ} (hcomponent : NegativeRadialComponent E l h)
    (hr : r ∈ radialTailInterval D side (morseChainSeam Q side Q.index))
    (hneg : deriv D.w r < 0) (hrnew : R * r ∈ Ioo l h) :
    ∃ n : ℕ, Q.index ≤ n ∧
      let a := Q.radius side n (morseLeftTurn (morseChainA Q n) (morseChainB Q n))
      let b := Q.radius side n (morseRightTurn (morseChainA Q n) (morseChainB Q n))
      l = R * a ∧ h = R * b ∧
        Icc a b ⊆ radialTailInterval D side (morseChainSeam Q side Q.index) := by
  obtain ⟨n, hn, x, hx, hrx⟩ :=
    morseRealization_negative_tail_model hreal side le_rfl hr hneg
  have hxin := (morseRealization_negative_at_radius_iff hreal hσ side hn hx).mp
    (by simpa only [hrx] using hneg)
  obtain ⟨hleft, hab, hright⟩ := morseRealization_turns_retained hreal side hn
  have hsub := Icc_subset_Icc hleft.le hright.le
  have ha := hsub (left_mem_Icc.mpr hab.le)
  have hb := hsub (right_mem_Icc.mpr hab.le)
  have hmono := hreal.radius_strictMonoOn side n hn
  have hrmodel : r ∈ Ioo
      (Q.radius side n (morseLeftTurn (morseChainA Q n) (morseChainB Q n)))
      (Q.radius side n (morseRightTurn (morseChainA Q n) (morseChainB Q n))) := by
    rw [hrx]
    exact ⟨hmono ha hx hxin.1, hmono hx hb hxin.2⟩
  have hmodel := (morseRealization_model_return hreal hσ side hn).1
  have hclosed := negativeRadialComponent_closed_subset_tail hmodel hrmodel hr
    (morseRealization_seam_deriv_pos hreal hσ side (le_refl Q.index))
  have htail : radialTailInterval D side (morseChainSeam Q side Q.index) =
      Ioo (if side then morseChainSeam Q side Q.index else D.a)
        (if side then D.b else morseChainSeam Q side Q.index) := by
    cases side <;> rfl
  have hscaled := (negativeRadialComponent_travel_of_tail_identity (E := E) hR hH hmodel
    (hcore _ (hclosed (left_mem_Icc.mpr hmodel.2.1.le))).1
    (hcore _ (hclosed (right_mem_Icc.mpr hmodel.2.1.le))).2
    hreal.geometry.2.2.1.1 hE
    (by simpa only [htail] using hclosed)
    (by simpa only [htail] using hprofile)).1
  have heq := negativeRadialComponent_unique_of_mem hcomponent hscaled hrnew
    ⟨mul_lt_mul_of_pos_left hrmodel.1 hR, mul_lt_mul_of_pos_left hrmodel.2 hR⟩
  exact ⟨n, hn, heq.1, heq.2, hclosed⟩

/-- Every actual negative component of the retained `Γ` is the central
one or a scaled turning interval from the same selected Morse family.
The tail alternative retains the precise index and the closed tail
inclusion needed by the uniform optical estimate. -/
theorem retainedReference_negative_component_identification
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {l h : ℝ} (hcomponent : NegativeRadialComponent Γ.reference l h) :
    (l = centralRadius (-sqrt centralOscillatorA) ∧
      h = centralRadius (sqrt centralOscillatorA)) ∨
    ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
      let a := S.chain.radius side n
        (morseLeftTurn (morseChainA S.chain n) (morseChainB S.chain n))
      let b := S.chain.radius side n
        (morseRightTurn (morseChainA S.chain n) (morseChainB S.chain n))
      let R := if side then P.pair.radiusR else P.pair.radiusL
      l = R * a ∧ h = R * b ∧
        Icc a b ⊆ radialTailInterval (S.family S.sigma) side (S.entry side S.chain.index) := by
  let D := S.family S.sigma
  let G := P.toEntryPair hS hband
  have hGL : G.radiusL = P.pair.radiusL := rfl
  have hGR : G.radiusR = P.pair.radiusR := rfl
  have hGp : G.profile = P.pair.profile := rfl
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hE : ContDiff ℝ ∞ Γ.reference.w := hΓ.2.1.choose_spec.1.2.2.1.1
  obtain ⟨e, N, hN, hlabels, hindex, hcells, hlocal, hleft, hright, hfibers, ha, hb⟩ :=
    hcoordinates
  have hentry (side : Bool) :
      S.entry side S.chain.index = morseChainSeam S.chain side S.chain.index :=
    (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.2.1
  have hc : S.entry false S.chain.index ∈ radialCore D :=
    (hS.2.2.2.2.2 false S.chain.index 2 le_rfl (by decide) hband).2.1
  have hd : S.entry true S.chain.index ∈ radialCore D :=
    (hS.2.2.2.2.2 true S.chain.index 2 le_rfl (by decide) hband).2.1
  have hRR : 0 < G.radiusR := G.radiusL_pos.trans_le G.radius_order
  have hDb : 0 < D.b := hreal.geometry.1.trans hreal.geometry.2.1
  have hleftCore (s : ℝ) (hs : s ∈ Ioo D.a (S.entry false S.chain.index)) :
      G.radiusL * s ∈ radialCore Γ.reference := by
    change Γ.reference.a < G.radiusL * s ∧ G.radiusL * s < Γ.reference.b
    rw [ha, hb]
    exact ⟨mul_lt_mul_of_pos_left hs.1 G.radiusL_pos,
      (mul_lt_mul_of_pos_left (hs.2.trans hc.2) G.radiusL_pos).trans_le
        (mul_le_mul_of_nonneg_right G.radius_order hDb.le)⟩
  have hrightCore (s : ℝ) (hs : s ∈ Ioo (S.entry true S.chain.index) D.b) :
      G.radiusR * s ∈ radialCore Γ.reference := by
    change Γ.reference.a < G.radiusR * s ∧ G.radiusR * s < Γ.reference.b
    rw [ha, hb]
    exact ⟨(mul_le_mul_of_nonneg_right G.radius_order hreal.geometry.1.le).trans_lt
      (mul_lt_mul_of_pos_left (hd.1.trans hs.1) hRR),
      mul_lt_mul_of_pos_left hs.2 hRR⟩
  let r := (l + h) / 2
  have hr : r ∈ Ioo l h := by
    dsimp only [r]
    constructor <;> linarith only [hcomponent.2.1]
  have hrG : r ∈ Ioo (G.radiusL * D.a) (G.radiusR * D.b) := by
    have hrE : Γ.reference.a < r ∧ r < Γ.reference.b :=
      ⟨hcomponent.1.trans hr.1, hr.2.trans hcomponent.2.2.1⟩
    rw [ha, hb, ← hGL, ← hGR] at hrE
    exact hrE
  have hnegG : deriv G.profile r < 0 := by
    have h0 := hcomponent.2.2.2.2.2 r hr
    rw [hw, ← hGp] at h0
    exact h0
  rcases G.negative_deriv_cases hq hrG hnegG with hL | hC | hR
  · obtain ⟨s, hs, hrs, hsneg⟩ := hL
    have hscaled := scaled_morse_component_identification (E := Γ.reference)
      (R := G.radiusL) (H := G.heightL) hreal hS.2.2.1 false
      G.radiusL_pos G.heightL_pos hE
      (by simpa only [radialTailInterval, Bool.false_eq_true, ↓reduceIte, ← hentry false]
        using hleftCore)
      (by
        intro t ht
        rw [hw]
        exact (G.left_tail t (by simpa only
          [radialTailInterval, Bool.false_eq_true, ↓reduceIte, ← hentry false] using ht)).1)
      hcomponent
      (by simpa only [radialTailInterval, Bool.false_eq_true, ↓reduceIte, ← hentry false]
        using hs) hsneg (by rw [← hrs]; exact hr)
    obtain ⟨n, hn, hl, hh, hclosed⟩ := hscaled
    exact Or.inr ⟨false, n, hn, hl, hh, by simpa only [hentry] using hclosed⟩
  · obtain ⟨hrmiddle, hnegCentral⟩ := hC
    have hrpos : 0 < r := (exp_pos K.left).trans hrmiddle.1
    have hx : centralModelCoordinate r ^ 2 < centralOscillatorA := by
      apply (centralRadialProfile_deriv_neg_iff (by norm_num : (0 : ℝ) < 1) _).mp
      rw [centralRadius_modelCoordinate hrpos]
      exact hnegCentral
    have hxI := sq_lt.mp hx
    have hrcentral : r ∈ Ioo (centralRadius (-sqrt centralOscillatorA))
        (centralRadius (sqrt centralOscillatorA)) :=
      ⟨(strictMono_centralRadius hxI.1).trans_eq (centralRadius_modelCoordinate hrpos),
        (centralRadius_modelCoordinate hrpos).symm.trans_lt (strictMono_centralRadius hxI.2)⟩
    have hcentral : NegativeRadialComponent Γ.reference
        (centralRadius (-sqrt centralOscillatorA)) (centralRadius (sqrt centralOscillatorA)) := by
      simpa only [NegativeRadialComponent, ha, hb, hw, hGL, hGR, hGp] using
        (G.central_model_return hq hc hd).1
    exact Or.inl (negativeRadialComponent_unique_of_mem hcomponent hcentral hr hrcentral)
  · obtain ⟨s, hs, hrs, hsneg⟩ := hR
    have hscaled := scaled_morse_component_identification (E := Γ.reference)
      (R := G.radiusR) (H := G.heightR) hreal hS.2.2.1 true
      hRR G.heightR_pos hE
      (by simpa only [radialTailInterval, ↓reduceIte, ← hentry true] using hrightCore)
      (by
        intro t ht
        rw [hw]
        exact (G.right_tail t (by simpa only
          [radialTailInterval, ↓reduceIte, ← hentry true] using ht)).1)
      hcomponent
      (by simpa only [radialTailInterval, ↓reduceIte, ← hentry true] using hs)
      hsneg (by rw [← hrs]; exact hr)
    obtain ⟨n, hn, hl, hh, hclosed⟩ := hscaled
    exact Or.inr ⟨true, n, hn, hl, hh, by simpa only [hentry] using hclosed⟩

end ContinuousFlexibility.Radial
