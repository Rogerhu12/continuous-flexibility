import ContinuousFlexibility.Radial.SeedPureTail
import ContinuousFlexibility.Radial.SeedOrientedGluing
import ContinuousFlexibility.Radial.SeedLogSlopeLower

/-! # Replacing the inward part of a pure natural tail -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- A positive increasing homogeneous pair may replace the inward side,
provided the complete profile and height germs agree at the splice. -/
theorem SeedPureTail.replace_inward_retaining_logSlope {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedPureTail D right entry u)
    (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    {W U : ℝ → ℝ} {splice cut c a p : ℝ}
    (hsplice : if right then splice < entry else entry < splice)
    (hcut : 0 < cut) (hcutsplice : if right then cut ≤ splice else splice ≤ cut)
    (hW : ContDiffOn ℝ ∞ W (Ioi 0)) (hU : ContDiffOn ℝ ∞ U (Ioi 0))
    (hpos : ∀ r, 0 < r → 0 < W r)
    (hderiv : ∀ r, 0 < r → 0 < deriv W r)
    (hode : ∀ r, 0 < r → radialJacobi 4 W U r = 0)
    (hmatchW : W =ᶠ[𝓝 splice] T.profile) (hmatchU : U =ᶠ[𝓝 splice] T.height)
    (hc : 0 < c) (ha : a ≠ 0) (hp : p ^ 2 = 4)
    (hpure : ∀ r, 0 < r → (if right then r < cut else cut < r) →
      W r = c * r ∧ U r = a * r ^ p) :
    ∃ V : SeedPureTail D right entry u, V.mode = p ∧ V.cut = cut ∧
      (∀ r, (if right then splice ≤ r else r ≤ splice) →
        V.profile =ᶠ[𝓝 r] T.profile ∧ V.height =ᶠ[𝓝 r] T.height) ∧
      (∀ r, 0 < r → 0 < deriv T.profile r → 0 < deriv V.profile r) ∧
      ∀ ν r, ν * W r ≤ r * deriv W r →
        ν * T.profile r ≤ r * deriv T.profile r →
        ν * V.profile r ≤ r * deriv V.profile r := by
  have hdomain (r : ℝ) (hr : r ∈ seedConeTailDomain D right) : 0 < r := by
    cases right
    · exact hD.1.trans hr
    · exact hr.1
  have houtzero (r : ℝ) (hr : if right then D.b ≤ r else r ≤ D.a) :
      if right then splice ≤ r else r ≤ splice := by
    cases right
    · exact hr.trans (hentry.1.trans hsplice).le
    · exact (hsplice.trans hentry.2).le.trans hr
  have houttail (r : ℝ) (hr : r ∈ radialTailInterval D right entry) :
      if right then splice ≤ r else r ≤ splice := by
    cases right
    · exact (hr.2.trans hsplice).le
    · exact (hsplice.trans hr.1).le
  have hcutentry : if right then cut < entry else entry < cut := by
    cases right
    · exact hsplice.trans_le hcutsplice
    · exact hcutsplice.trans_lt hsplice
  refine ⟨{
    profile := seedOrientedGlue right splice W T.profile
    height := seedOrientedGlue right splice U T.height
    profile_smooth := contDiffOn_seedOrientedGlue hW T.profile_smooth hmatchW
    height_smooth := contDiffOn_seedOrientedGlue hU T.height_smooth hmatchU
    outward_zero := ?_
    tail_eq := ?_
    positive := ?_
    simple_critical := ?_
    homogeneous := ?_
    cut := cut
    cut_pos := hcut
    cut_order := hcutentry
    cone_scale := c
    amplitude := a
    mode := p
    scale_pos := hc
    amplitude_ne_zero := ha
    mode_sq := hp
    pure_eq := ?_
  }, rfl, rfl, ?_, ?_, ?_⟩
  · intro r hr
    have hside := houtzero r hr
    rw [(seedOrientedGlue_outward_germ hmatchW hside).eq_of_nhds,
      (seedOrientedGlue_outward_germ hmatchU hside).eq_of_nhds]
    exact T.outward_zero r hr
  · intro r hr
    have hside := houttail r hr
    rw [(seedOrientedGlue_outward_germ hmatchW hside).eq_of_nhds,
      (seedOrientedGlue_outward_germ hmatchU hside).eq_of_nhds]
    exact T.tail_eq r hr
  · intro r hr
    rcases seedOrientedGlue_sides right splice r with hi | ho
    · rw [(seedOrientedGlue_inward_germ hmatchW hi).eq_of_nhds]
      exact hpos r (hdomain r hr)
    · rw [(seedOrientedGlue_outward_germ hmatchW ho).eq_of_nhds]
      exact T.positive r hr
  · intro r hr hz
    rcases seedOrientedGlue_sides right splice r with hi | ho
    · rw [(seedOrientedGlue_inward_germ hmatchW hi).deriv_eq] at hz
      exact False.elim ((hderiv r (hdomain r hr)).ne' hz)
    · have hg := seedOrientedGlue_outward_germ hmatchW ho
      rw [hg.deriv_eq] at hz
      rw [hg.deriv.deriv_eq]
      exact T.simple_critical r hr hz
  · intro r hr
    rcases seedOrientedGlue_sides right splice r with hi | ho
    · rw [radialJacobi_eq_of_germs (seedOrientedGlue_inward_germ hmatchW hi)
        (seedOrientedGlue_inward_germ hmatchU hi)]
      exact hode r (hdomain r hr)
    · rw [radialJacobi_eq_of_germs (seedOrientedGlue_outward_germ hmatchW ho)
        (seedOrientedGlue_outward_germ hmatchU ho)]
      exact T.homogeneous r hr
  · intro r hr hrc
    have hside : if right then r ≤ splice else splice ≤ r := by
      cases right
      · exact hcutsplice.trans hrc.le
      · exact hrc.le.trans hcutsplice
    rw [(seedOrientedGlue_inward_germ hmatchW hside).eq_of_nhds,
      (seedOrientedGlue_inward_germ hmatchU hside).eq_of_nhds]
    exact hpure r hr hrc
  · intro r hr
    exact ⟨seedOrientedGlue_outward_germ hmatchW hr,
      seedOrientedGlue_outward_germ hmatchU hr⟩
  · intro r hp hd
    rcases seedOrientedGlue_sides right splice r with hi | ho
    · rw [(seedOrientedGlue_inward_germ hmatchW hi).deriv_eq]
      exact hderiv r hp
    · rw [(seedOrientedGlue_outward_germ hmatchW ho).deriv_eq]
      exact hd
  · intro ν r hWlower hTlower
    rcases seedOrientedGlue_sides right splice r with hi | ho
    · exact logSlope_lower_of_germ (seedOrientedGlue_inward_germ hmatchW hi) hWlower
    · exact logSlope_lower_of_germ (seedOrientedGlue_outward_germ hmatchW ho) hTlower

/-- The original retained replacement interface. -/
theorem SeedPureTail.replace_inward_retaining {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedPureTail D right entry u)
    (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    {W U : ℝ → ℝ} {splice cut c a p : ℝ}
    (hsplice : if right then splice < entry else entry < splice)
    (hcut : 0 < cut) (hcutsplice : if right then cut ≤ splice else splice ≤ cut)
    (hW : ContDiffOn ℝ ∞ W (Ioi 0)) (hU : ContDiffOn ℝ ∞ U (Ioi 0))
    (hpos : ∀ r, 0 < r → 0 < W r)
    (hderiv : ∀ r, 0 < r → 0 < deriv W r)
    (hode : ∀ r, 0 < r → radialJacobi 4 W U r = 0)
    (hmatchW : W =ᶠ[𝓝 splice] T.profile) (hmatchU : U =ᶠ[𝓝 splice] T.height)
    (hc : 0 < c) (ha : a ≠ 0) (hp : p ^ 2 = 4)
    (hpure : ∀ r, 0 < r → (if right then r < cut else cut < r) →
      W r = c * r ∧ U r = a * r ^ p) :
    ∃ V : SeedPureTail D right entry u, V.mode = p ∧ V.cut = cut ∧
      (∀ r, (if right then splice ≤ r else r ≤ splice) →
        V.profile =ᶠ[𝓝 r] T.profile ∧ V.height =ᶠ[𝓝 r] T.height) ∧
      ∀ r, 0 < r → 0 < deriv T.profile r → 0 < deriv V.profile r := by
  obtain ⟨V, hm, hc', hg, hd, _⟩ := T.replace_inward_retaining_logSlope
    hD hentry hsplice hcut hcutsplice hW hU hpos hderiv hode hmatchW hmatchU hc ha hp hpure
  exact ⟨V, hm, hc', hg, hd⟩

/-- The original inward-replacement interface. -/
theorem SeedPureTail.replace_inward {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedPureTail D right entry u)
    (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    {W U : ℝ → ℝ} {splice cut c a p : ℝ}
    (hsplice : if right then splice < entry else entry < splice)
    (hcut : 0 < cut) (hcutsplice : if right then cut ≤ splice else splice ≤ cut)
    (hW : ContDiffOn ℝ ∞ W (Ioi 0)) (hU : ContDiffOn ℝ ∞ U (Ioi 0))
    (hpos : ∀ r, 0 < r → 0 < W r)
    (hderiv : ∀ r, 0 < r → 0 < deriv W r)
    (hode : ∀ r, 0 < r → radialJacobi 4 W U r = 0)
    (hmatchW : W =ᶠ[𝓝 splice] T.profile) (hmatchU : U =ᶠ[𝓝 splice] T.height)
    (hc : 0 < c) (ha : a ≠ 0) (hp : p ^ 2 = 4)
    (hpure : ∀ r, 0 < r → (if right then r < cut else cut < r) →
      W r = c * r ∧ U r = a * r ^ p) :
    ∃ V : SeedPureTail D right entry u, V.mode = p := by
  obtain ⟨V, hm, _, _, _⟩ := T.replace_inward_retaining hD hentry hsplice hcut hcutsplice
    hW hU hpos hderiv hode hmatchW hmatchU hc ha hp hpure
  exact ⟨V, hm⟩

end ContinuousFlexibility.Radial
