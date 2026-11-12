import ContinuousFlexibility.Radial.SeedGluedPair
import ContinuousFlexibility.Radial.SeedLogSlopeLower

/-!
# Construction of the global seed from two canonical pure tails

The left tail is compressed and the right tail expanded. Their exact
pure cone modes then agree with the central pair after two positive
profile rescalings and two nonzero field rescalings. Full germs at the
cuts preserve the ordinary differential equation and every derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open Statements

theorem exists_seedGluedPair_retaining_logSlope {D : ReferenceData} {c d : ℝ} {uL uR : ℝ → ℝ}
    (hD : RadialProfileGeometry D) (hc : c ∈ radialCore D) (hd : d ∈ radialCore D)
    (TL : SeedPureTail D false c uL) (TR : SeedPureTail D true d uR)
    (hTL : TL.mode = 2) (hTR : TR.mode = -2)
    (K : SeedCentralCutoff) {q : ℝ} (hq : 0 < q) :
    ∃ G : SeedGluedPair D c d uL uR K q,
      (∀ r, 0 < r → r ≤ G.radiusL * TL.cut →
        G.profile =ᶠ[𝓝 r] seedRescale G.radiusL (G.heightL * G.radiusL) TL.profile ∧
        G.height =ᶠ[𝓝 r] seedRescale G.radiusL G.amplitudeL TL.height) ∧
      (∀ r, G.radiusR * TR.cut ≤ r →
        G.profile =ᶠ[𝓝 r] seedRescale G.radiusR (G.heightR * G.radiusR) TR.profile ∧
        G.height =ᶠ[𝓝 r] seedRescale G.radiusR G.amplitudeR TR.height) ∧
      G.radiusL * TL.cut < exp (K.left - q - 4) ∧
      exp (K.right + q + 4) < G.radiusR * TR.cut ∧
      ((∀ r, 0 < r → c ≤ r → 0 < deriv TL.profile r) →
        ∀ r ∈ Icc (G.radiusL * c) (exp K.left), 0 < deriv G.profile r) ∧
      ((∀ r, 0 < r → r ≤ d → 0 < deriv TR.profile r) →
        ∀ r ∈ Icc (exp K.right) (G.radiusR * d), 0 < deriv G.profile r) ∧
      ((∀ r, 0 < r → c ≤ r →
          (3 / 4 : ℝ) * TL.profile r ≤ r * deriv TL.profile r) →
        ∀ r ∈ Icc (G.radiusL * c) (exp K.left),
          (3 / 4 : ℝ) * G.profile r ≤ r * deriv G.profile r) ∧
      ((∀ r, 0 < r → r ≤ d →
          (3 / 4 : ℝ) * TR.profile r ≤ r * deriv TR.profile r) →
        ∀ r ∈ Icc (exp K.right) (G.radiusR * d),
          (3 / 4 : ℝ) * G.profile r ≤ r * deriv G.profile r) := by
  obtain ⟨cL, cR, aL, aR, hcL, hcR, haL, haR, hconeL, hconeR⟩ := K.exact_cones
  let zL := exp (K.left - q - 4)
  let zR := exp (K.right + q + 4)
  have hzL : 0 < zL := exp_pos _
  have hzR : 0 < zR := exp_pos _
  have hzLone : zL < 1 := by
    dsimp only [zL]
    rw [exp_lt_one_iff]
    linarith [K.left_neg]
  have honezR : 1 < zR := by
    dsimp only [zR]
    rw [one_lt_exp_iff]
    linarith [K.right_pos]
  have hzLR : zL < zR := hzLone.trans honezR
  let RL := min 1 (zL / (2 * TL.cut))
  let RR := max 1 (2 * zR / TR.cut)
  have hRL : 0 < RL := lt_min (by norm_num) (div_pos hzL (mul_pos (by norm_num) TL.cut_pos))
  have hRR : 0 < RR := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have horder : RL ≤ RR := (min_le_left _ _).trans (le_max_left _ _)
  have hcutL : RL * TL.cut < zL := by
    have hh := mul_le_mul_of_nonneg_right
      (min_le_right (1 : ℝ) (zL / (2 * TL.cut))) TL.cut_pos.le
    have he : zL / (2 * TL.cut) * TL.cut = zL / 2 := by
      field_simp [TL.cut_pos.ne'] <;> ring
    rw [he] at hh
    change RL * TL.cut ≤ zL / 2 at hh
    linarith
  have hcutR : zR < RR * TR.cut := by
    have hh := mul_le_mul_of_nonneg_right
      (le_max_right (1 : ℝ) (2 * zR / TR.cut)) TR.cut_pos.le
    have he : (2 * zR / TR.cut) * TR.cut = 2 * zR := by
      field_simp [TR.cut_pos.ne'] <;> ring
    rw [he] at hh
    change 2 * zR ≤ RR * TR.cut at hh
    linarith
  have hLc : c < TL.cut := by simpa using TL.cut_order
  have hRd : TR.cut < d := by simpa using TR.cut_order
  have heL : RL * c < zL := (mul_lt_mul_of_pos_left hLc hRL).trans hcutL
  have heR : zR < RR * d := hcutR.trans (mul_lt_mul_of_pos_left hRd hRR)
  have ha : 0 < RL * D.a := mul_pos hRL hD.1
  have hbefore : RL * D.a < zL :=
    (mul_lt_mul_of_pos_left hc.1 hRL).trans heL
  have hafter : zR < RR * D.b :=
    heR.trans (mul_lt_mul_of_pos_left hd.2 hRR)
  let HL := cL / TL.cone_scale
  let HR := cR / TR.cone_scale
  let AL := aL * RL ^ (2 : ℝ) / TL.amplitude
  let AR := aR * RR ^ (-2 : ℝ) / TR.amplitude
  have hHL : 0 < HL := div_pos hcL TL.scale_pos
  have hHR : 0 < HR := div_pos hcR TR.scale_pos
  have hAL : AL ≠ 0 :=
    div_ne_zero (mul_ne_zero haL.ne' (rpow_pos_of_pos hRL _).ne') TL.amplitude_ne_zero
  have hAR : AR ≠ 0 :=
    div_ne_zero (mul_ne_zero haR.ne' (rpow_pos_of_pos hRR _).ne') TR.amplitude_ne_zero
  let WL := seedRescale RL (HL * RL) TL.profile
  let UL := seedRescale RL AL TL.height
  let WR := seedRescale RR (HR * RR) TR.profile
  let UR := seedRescale RR AR TR.height
  have hinvL (r : ℝ) : RL * (RL⁻¹ * r) = r := by
    rw [← mul_assoc, mul_inv_cancel₀ hRL.ne', one_mul]
  have hinvR (r : ℝ) : RR * (RR⁻¹ * r) = r := by
    rw [← mul_assoc, mul_inv_cancel₀ hRR.ne', one_mul]
  have hlogL : zL < exp (K.left - 1) := by
    apply exp_lt_exp.mpr
    linarith
  have hlogR : exp (K.right + 1) < zR := by
    apply exp_lt_exp.mpr
    linarith
  have hgL : ∀ᶠ r in 𝓝 zL,
      WL r = K.profile r ∧ UL r = K.height r := by
    filter_upwards [isOpen_Ioo.mem_nhds (show zL ∈
      Ioo (RL * TL.cut) (exp (K.left - 1)) from ⟨hcutL, hlogL⟩)] with r hr
    have hp : 0 < r := (mul_pos hRL TL.cut_pos).trans hr.1
    have hcut : TL.cut < RL⁻¹ * r := by
      have hh : TL.cut < r / RL := (lt_div_iff₀ hRL).mpr
        (by simpa only [mul_comm] using hr.1)
      simpa only [div_eq_mul_inv, mul_comm] using hh
    have ht := TL.pure_eq (RL⁻¹ * r) (mul_pos (inv_pos.mpr hRL) hp)
      (by simpa using hcut)
    have htu : TL.height (RL⁻¹ * r) = TL.amplitude * (RL⁻¹ * r) ^ (2 : ℝ) := by
      simpa only [hTL] using ht.2
    have hs := seedRescale_match_cone (c := cL) (a := aL) hRL hp
      TL.scale_pos.ne' TL.amplitude_ne_zero ht.1 htu
    have hlog : log r < K.left - 1 := (log_lt_iff_lt_exp hp).mpr hr.2
    have hm := hconeL r hp hlog
    exact ⟨hs.1.trans hm.1.symm, hs.2.trans hm.2.symm⟩
  have hgR : ∀ᶠ r in 𝓝 zR,
      K.profile r = WR r ∧ K.height r = UR r := by
    filter_upwards [isOpen_Ioo.mem_nhds (show zR ∈
      Ioo (exp (K.right + 1)) (RR * TR.cut) from ⟨hlogR, hcutR⟩)] with r hr
    have hp : 0 < r := (exp_pos _).trans hr.1
    have hcut : RR⁻¹ * r < TR.cut := by
      have hh : r / RR < TR.cut := (div_lt_iff₀ hRR).mpr
        (by simpa only [mul_comm] using hr.2)
      simpa only [div_eq_mul_inv, mul_comm] using hh
    have ht := TR.pure_eq (RR⁻¹ * r) (mul_pos (inv_pos.mpr hRR) hp)
      (by simpa using hcut)
    have htu : TR.height (RR⁻¹ * r) = TR.amplitude * (RR⁻¹ * r) ^ (-2 : ℝ) := by
      simpa only [hTR] using ht.2
    have hs := seedRescale_match_cone (c := cR) (a := aR) hRR hp
      TR.scale_pos.ne' TR.amplitude_ne_zero ht.1 htu
    have hlog : K.right + 1 < log r := (lt_log_iff_exp_lt hp).mpr hr.1
    have hm := hconeR r hp hlog
    exact ⟨hm.1.trans hs.1.symm, hm.2.trans hs.2.symm⟩
  have hwL : WL =ᶠ[𝓝 zL] K.profile := hgL.mono (fun _ h => h.1)
  have huL : UL =ᶠ[𝓝 zL] K.height := hgL.mono (fun _ h => h.2)
  have hwR : K.profile =ᶠ[𝓝 zR] WR := hgR.mono (fun _ h => h.1)
  have huR : K.height =ᶠ[𝓝 zR] UR := hgR.mono (fun _ h => h.2)
  let W₀ := seedThreeGlue zL zR WL K.profile WR
  let U₀ := seedThreeGlue zL zR UL K.height UR
  let W := seedZeroBelow W₀
  let U := seedZeroBelow U₀
  have hleft (r : ℝ) (hp : 0 < r) (hr : r ≤ zL) :
      W =ᶠ[𝓝 r] WL ∧ U =ᶠ[𝓝 r] UL :=
    ⟨(seedZeroBelow_germ hp).trans (seedThreeGlue_left_germ hzLR hwL hwR hr),
      (seedZeroBelow_germ hp).trans (seedThreeGlue_left_germ hzLR huL huR hr)⟩
  have hmiddle (r : ℝ) (hr : r ∈ Icc zL zR) :
      W =ᶠ[𝓝 r] K.profile ∧ U =ᶠ[𝓝 r] K.height :=
    ⟨(seedZeroBelow_germ (hzL.trans_le hr.1)).trans
        (seedThreeGlue_middle_germ hzLR hwL hwR hr),
      (seedZeroBelow_germ (hzL.trans_le hr.1)).trans
        (seedThreeGlue_middle_germ hzLR huL huR hr)⟩
  have hright (r : ℝ) (hr : zR ≤ r) :
      W =ᶠ[𝓝 r] WR ∧ U =ᶠ[𝓝 r] UR :=
    ⟨(seedZeroBelow_germ (hzR.trans_le hr)).trans
        (seedThreeGlue_right_germ hzLR hwL hwR hr),
      (seedZeroBelow_germ (hzR.trans_le hr)).trans
        (seedThreeGlue_right_germ hzLR huL huR hr)⟩
  have hzeroLeft (r : ℝ) (hr : r ≤ RL * D.a) :
      W₀ r = 0 ∧ U₀ r = 0 := by
    have hrL : r ≤ zL := hr.trans hbefore.le
    have hx : RL⁻¹ * r ≤ D.a := by
      have hh : r / RL ≤ D.a := (div_le_iff₀ hRL).mpr
        (by simpa only [mul_comm] using hr)
      simpa only [div_eq_mul_inv, mul_comm] using hh
    have hz := TL.outward_zero (RL⁻¹ * r) (by simpa using hx)
    have hw := (seedThreeGlue_left_germ hzLR hwL hwR hrL).eq_of_nhds
    have hu := (seedThreeGlue_left_germ hzLR huL huR hrL).eq_of_nhds
    constructor
    · change seedThreeGlue zL zR WL K.profile WR r = 0
      rw [hw]
      change HL * RL * TL.profile (RL⁻¹ * r) = 0
      rw [hz.1, mul_zero]
    · change seedThreeGlue zL zR UL K.height UR r = 0
      rw [hu]
      change AL * TL.height (RL⁻¹ * r) = 0
      rw [hz.2, mul_zero]
  have hzeroRight (r : ℝ) (hr : RR * D.b ≤ r) :
      W r = 0 ∧ U r = 0 := by
    have hrR : zR ≤ r := hafter.le.trans hr
    have hx : D.b ≤ RR⁻¹ * r := by
      have hh : D.b ≤ r / RR := (le_div_iff₀ hRR).mpr
        (by simpa only [mul_comm] using hr)
      simpa only [div_eq_mul_inv, mul_comm] using hh
    have hz := TR.outward_zero (RR⁻¹ * r) (by simpa using hx)
    have hg := hright r hrR
    constructor
    · rw [hg.1.eq_of_nhds]
      change HR * RR * TR.profile (RR⁻¹ * r) = 0
      rw [hz.1, mul_zero]
    · rw [hg.2.eq_of_nhds]
      change AR * TR.height (RR⁻¹ * r) = 0
      rw [hz.2, mul_zero]
  have hWs : ContDiff ℝ ∞ W :=
    contDiff_seedZeroBelow ha
      (contDiffOn_seedThreeGlue hzLR hwL hwR
        (contDiffOn_seedRescale hRL TL.profile_smooth) K.profile_smooth
        (contDiffOn_seedRescale hRR TR.profile_smooth))
      (fun r _ hr => (hzeroLeft r hr.le).1)
  have hUs : ContDiff ℝ ∞ U :=
    contDiff_seedZeroBelow ha
      (contDiffOn_seedThreeGlue hzLR huL huR
        (contDiffOn_seedRescale hRL TL.height_smooth) K.height_smooth
        (contDiffOn_seedRescale hRR TR.height_smooth))
      (fun r _ hr => (hzeroLeft r hr.le).2)
  have hflat (r : ℝ) (hr : r ≤ RL * D.a ∨ RR * D.b ≤ r) :
      W r = 0 ∧ U r = 0 := by
    rcases hr with hr | hr
    · by_cases hp : 0 < r
      · have hz := hzeroLeft r hr
        exact ⟨(seedZeroBelow_germ hp).eq_of_nhds.trans hz.1,
          (seedZeroBelow_germ hp).eq_of_nhds.trans hz.2⟩
      · simp only [W, U, seedZeroBelow, if_neg hp, and_self]
    · exact hzeroRight r hr
  have hproperties (r : ℝ) (hr : r ∈ Ioo (RL * D.a) (RR * D.b)) :
      0 < W r ∧ radialJacobi 4 W U r = 0 ∧
        (deriv W r = 0 → deriv (deriv W) r ≠ 0) := by
    have hp : 0 < r := ha.trans hr.1
    by_cases hl : r ≤ zL
    · have hg := hleft r hp hl
      have hx : D.a < RL⁻¹ * r := by
        have hh : D.a < r / RL := (lt_div_iff₀ hRL).mpr
          (by simpa only [mul_comm] using hr.1)
        simpa only [div_eq_mul_inv, mul_comm] using hh
      have hxmem : RL⁻¹ * r ∈ seedConeTailDomain D false := by
        simpa only [seedConeTailDomain, Bool.false_eq_true, ↓reduceIte, mem_Ioi] using hx
      have hxp : 0 < RL⁻¹ * r := hD.1.trans hx
      refine ⟨?_, ?_, ?_⟩
      · rw [hg.1.eq_of_nhds]
        exact mul_pos (mul_pos hHL hRL) (TL.positive _ hxmem)
      · rw [radialJacobi_eq_of_germs hg.1 hg.2]
        have hh := radialJacobi_seedRescale (R := RL) (H := HL) (A := AL)
          (a := 4) (w := TL.profile) (u := TL.height) hRL.ne' hxp.ne'
        rw [hinvL r, TL.homogeneous _ hxmem, mul_zero] at hh
        exact hh
      · intro hz
        rw [hg.1.deriv.deriv_eq]
        apply seedRescale_simple_critical hRL.ne' (mul_pos hHL hRL).ne'
          (TL.simple_critical _ hxmem)
        rwa [← hg.1.deriv_eq]
    · by_cases hh : zR ≤ r
      · have hg := hright r hh
        have hx : RR⁻¹ * r < D.b := by
          have hh' : r / RR < D.b := (div_lt_iff₀ hRR).mpr
            (by simpa only [mul_comm] using hr.2)
          simpa only [div_eq_mul_inv, mul_comm] using hh'
        have hxp : 0 < RR⁻¹ * r := mul_pos (inv_pos.mpr hRR) hp
        have hxmem : RR⁻¹ * r ∈ seedConeTailDomain D true := ⟨hxp, hx⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hg.1.eq_of_nhds]
          exact mul_pos (mul_pos hHR hRR) (TR.positive _ hxmem)
        · rw [radialJacobi_eq_of_germs hg.1 hg.2]
          have heq := radialJacobi_seedRescale (R := RR) (H := HR) (A := AR)
            (a := 4) (w := TR.profile) (u := TR.height) hRR.ne' hxp.ne'
          rw [hinvR r, TR.homogeneous _ hxmem, mul_zero] at heq
          exact heq
        · intro hz
          rw [hg.1.deriv.deriv_eq]
          apply seedRescale_simple_critical hRR.ne' (mul_pos hHR hRR).ne'
            (TR.simple_critical _ hxmem)
          rwa [← hg.1.deriv_eq]
      · have hg := hmiddle r ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hh).le⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hg.1.eq_of_nhds]
          exact K.profile_pos hp
        · rw [radialJacobi_eq_of_germs hg.1 hg.2]
          exact K.equation hp
        · intro hz
          rw [hg.1.deriv.deriv_eq]
          apply K.profile_simple_critical hp
          rwa [← hg.1.deriv_eq]
  refine ⟨{
    profile := W
    height := U
    radiusL := RL
    radiusR := RR
    heightL := HL
    heightR := HR
    amplitudeL := AL
    amplitudeR := AR
    radiusL_pos := hRL
    radius_order := horder
    heightL_pos := hHL
    heightR_pos := hHR
    amplitudeL_ne := hAL
    amplitudeR_ne := hAR
    geometry := ?_
    equation := fun r hr => (hproperties r hr).2.1
    left_entry := heL
    right_entry := heR
    middle_germ := fun r hr => hmiddle r ⟨hr.1.le, hr.2.le⟩
    left_increasing := by
      intro r hentry hretained
      have hp : 0 < r := (mul_pos hRL (hD.1.trans hc.1)).trans_le hentry
      by_cases hr : r ≤ zL
      · rw [(hleft r hp hr).1.deriv_eq]
        apply seedRescale_deriv_pos hRL (mul_pos hHL hRL)
        apply TL.inward_increasing _ (mul_pos (inv_pos.mpr hRL) hp)
        change c ≤ RL⁻¹ * r
        have h : c ≤ r / RL := (le_div_iff₀ hRL).mpr
          (by simpa only [mul_comm] using hentry)
        simpa only [div_eq_mul_inv, mul_comm] using h
      · have hz : r ≤ zR := hretained.trans (exp_le_exp.mpr
          (by linarith only [K.left_neg, K.right_pos, hq]))
        rw [(hmiddle r ⟨(lt_of_not_ge hr).le, hz⟩).1.deriv_eq]
        exact K.profile_deriv_pos hp (Or.inl ((log_le_iff_le_exp hp).mpr hretained))
    right_increasing := by
      intro r hretained hentry
      have hp : 0 < r := (exp_pos K.right).trans_le hretained
      by_cases hr : zR ≤ r
      · rw [(hright r hr).1.deriv_eq]
        apply seedRescale_deriv_pos hRR (mul_pos hHR hRR)
        apply TR.inward_increasing _ (mul_pos (inv_pos.mpr hRR) hp)
        change RR⁻¹ * r ≤ d
        have h : r / RR ≤ d := (div_le_iff₀ hRR).mpr
          (by simpa only [mul_comm] using hentry)
        simpa only [div_eq_mul_inv, mul_comm] using h
      · have hz : zL ≤ r := (exp_le_exp.mpr
          (by linarith only [K.left_neg, K.right_pos, hq])).trans hretained
        rw [(hmiddle r ⟨hz, (lt_of_not_ge hr).le⟩).1.deriv_eq]
        exact K.profile_deriv_pos hp (Or.inr ((le_log_iff_exp_le hp).mpr hretained))
    left_tail := ?_
    right_tail := ?_
  }, ?_, ?_, hcutL, hcutR, ?_, ?_, ?_, ?_⟩
  · refine ⟨ha, (hbefore.trans hzLR).trans hafter,
      ⟨hWs, fun r hr => (hflat r hr).1⟩,
      ⟨hUs, fun r hr => (hflat r hr).2⟩,
      fun r hr => (hproperties r hr).1, ?_,
      fun r hr => (hproperties r hr).2.2⟩
    have hmem : (1 : ℝ) ∈ Ioo (RL * D.a) (RR * D.b) :=
      ⟨hbefore.trans hzLone, honezR.trans hafter⟩
    refine ⟨1, hmem, ?_⟩
    change U 1 ≠ 0
    rw [(hmiddle 1 ⟨hzLone.le, honezR.le⟩).2.eq_of_nhds]
    exact (K.height_pos 1).ne'
  · intro r hr
    have hp : 0 < r := hD.1.trans hr.1
    have hg := hleft (RL * r) (mul_pos hRL hp)
      ((mul_lt_mul_of_pos_left hr.2 hRL).trans heL).le
    have ht := TL.tail_eq r (by simpa only [radialTailInterval, Bool.false_eq_true,
      ↓reduceIte] using hr)
    constructor
    · calc
        W (RL * r) = WL (RL * r) := hg.1.eq_of_nhds
        _ = (HL * RL) * TL.profile r := seedRescale_at_scaled hRL.ne' _ _ _
        _ = HL * RL * D.w r := by rw [ht.1]
    · calc
        U (RL * r) = UL (RL * r) := hg.2.eq_of_nhds
        _ = AL * TL.height r := seedRescale_at_scaled hRL.ne' _ _ _
        _ = AL * uL r := by rw [ht.2]
  · intro r hr
    have hp : 0 < r := (hD.1.trans hd.1).trans hr.1
    have hg := hright (RR * r)
      (heR.trans (mul_lt_mul_of_pos_left hr.1 hRR)).le
    have ht := TR.tail_eq r (by simpa only [radialTailInterval, ↓reduceIte] using hr)
    constructor
    · calc
        W (RR * r) = WR (RR * r) := hg.1.eq_of_nhds
        _ = (HR * RR) * TR.profile r := seedRescale_at_scaled hRR.ne' _ _ _
        _ = HR * RR * D.w r := by rw [ht.1]
    · calc
        U (RR * r) = UR (RR * r) := hg.2.eq_of_nhds
        _ = AR * TR.height r := seedRescale_at_scaled hRR.ne' _ _ _
        _ = AR * uR r := by rw [ht.2]
  · intro r hp hr
    exact hleft r hp (hr.trans hcutL.le)
  · intro r hr
    exact hright r (hcutR.le.trans hr)
  · intro hTLder r hr
    have hp : 0 < r := (mul_pos hRL (hD.1.trans hc.1)).trans_le hr.1
    by_cases hl : r ≤ zL
    · rw [(hleft r hp hl).1.deriv_eq]
      apply seedRescale_deriv_pos hRL (mul_pos hHL hRL)
      apply hTLder _ (mul_pos (inv_pos.mpr hRL) hp)
      have hx : c ≤ r / RL := (le_div_iff₀ hRL).mpr
        (by simpa only [mul_comm] using hr.1)
      simpa only [div_eq_mul_inv, mul_comm] using hx
    · have hLzR : exp K.left < zR := by
        change exp K.left < exp (K.right + q + 4)
        apply exp_lt_exp.mpr
        linarith [K.left_neg, K.right_pos]
      rw [(hmiddle r ⟨(lt_of_not_ge hl).le, hr.2.trans hLzR.le⟩).1.deriv_eq]
      apply K.profile_deriv_pos hp
      left
      simpa only [log_exp] using log_le_log hp hr.2
  · intro hTRder r hr
    have hp : 0 < r := (exp_pos K.right).trans_le hr.1
    by_cases hh : zR ≤ r
    · rw [(hright r hh).1.deriv_eq]
      apply seedRescale_deriv_pos hRR (mul_pos hHR hRR)
      apply hTRder _ (mul_pos (inv_pos.mpr hRR) hp)
      have hx : r / RR ≤ d := (div_le_iff₀ hRR).mpr
        (by simpa only [mul_comm] using hr.2)
      simpa only [div_eq_mul_inv, mul_comm] using hx
    · have hzLH : zL < exp K.right := by
        change exp (K.left - q - 4) < exp K.right
        apply exp_lt_exp.mpr
        linarith [K.left_neg, K.right_pos]
      rw [(hmiddle r ⟨hzLH.le.trans hr.1, (lt_of_not_ge hh).le⟩).1.deriv_eq]
      apply K.profile_deriv_pos hp
      right
      simpa only [log_exp] using log_le_log (exp_pos K.right) hr.1
  · intro hTLlower r hr
    have hp : 0 < r := (mul_pos hRL (hD.1.trans hc.1)).trans_le hr.1
    by_cases hl : r ≤ zL
    · apply logSlope_lower_of_germ (hleft r hp hl).1
      apply seedRescale_logSlope_lower (mul_pos hHL hRL).le
      apply hTLlower _ (mul_pos (inv_pos.mpr hRL) hp)
      have hx : c ≤ r / RL := (le_div_iff₀ hRL).mpr
        (by simpa only [mul_comm] using hr.1)
      simpa only [div_eq_mul_inv, mul_comm] using hx
    · have hLzR : exp K.left < zR := by
        change exp K.left < exp (K.right + q + 4)
        apply exp_lt_exp.mpr
        linarith [K.left_neg, K.right_pos]
      apply logSlope_lower_of_germ
        (hmiddle r ⟨(lt_of_not_ge hl).le, hr.2.trans hLzR.le⟩).1
      apply K.profile_logSlope_lower hp
      left
      simpa only [log_exp] using log_le_log hp hr.2
  · intro hTRlower r hr
    have hp : 0 < r := (exp_pos K.right).trans_le hr.1
    by_cases hh : zR ≤ r
    · apply logSlope_lower_of_germ (hright r hh).1
      apply seedRescale_logSlope_lower (mul_pos hHR hRR).le
      apply hTRlower _ (mul_pos (inv_pos.mpr hRR) hp)
      have hx : r / RR ≤ d := (div_le_iff₀ hRR).mpr
        (by simpa only [mul_comm] using hr.2)
      simpa only [div_eq_mul_inv, mul_comm] using hx
    · have hzLH : zL < exp K.right := by
        change exp (K.left - q - 4) < exp K.right
        apply exp_lt_exp.mpr
        linarith [K.left_neg, K.right_pos]
      apply logSlope_lower_of_germ
        (hmiddle r ⟨hzLH.le.trans hr.1, (lt_of_not_ge hh).le⟩).1
      apply K.profile_logSlope_lower hp
      right
      simpa only [log_exp] using log_le_log (exp_pos K.right) hr.1

/-- The original retained pair interface. -/
theorem exists_seedGluedPair_retaining {D : ReferenceData} {c d : ℝ} {uL uR : ℝ → ℝ}
    (hD : RadialProfileGeometry D) (hc : c ∈ radialCore D) (hd : d ∈ radialCore D)
    (TL : SeedPureTail D false c uL) (TR : SeedPureTail D true d uR)
    (hTL : TL.mode = 2) (hTR : TR.mode = -2)
    (K : SeedCentralCutoff) {q : ℝ} (hq : 0 < q) :
    ∃ G : SeedGluedPair D c d uL uR K q,
      (∀ r, 0 < r → r ≤ G.radiusL * TL.cut →
        G.profile =ᶠ[𝓝 r] seedRescale G.radiusL (G.heightL * G.radiusL) TL.profile ∧
        G.height =ᶠ[𝓝 r] seedRescale G.radiusL G.amplitudeL TL.height) ∧
      (∀ r, G.radiusR * TR.cut ≤ r →
        G.profile =ᶠ[𝓝 r] seedRescale G.radiusR (G.heightR * G.radiusR) TR.profile ∧
        G.height =ᶠ[𝓝 r] seedRescale G.radiusR G.amplitudeR TR.height) ∧
      G.radiusL * TL.cut < exp (K.left - q - 4) ∧
      exp (K.right + q + 4) < G.radiusR * TR.cut ∧
      ((∀ r, 0 < r → c ≤ r → 0 < deriv TL.profile r) →
        ∀ r ∈ Icc (G.radiusL * c) (exp K.left), 0 < deriv G.profile r) ∧
      ((∀ r, 0 < r → r ≤ d → 0 < deriv TR.profile r) →
        ∀ r ∈ Icc (exp K.right) (G.radiusR * d), 0 < deriv G.profile r) := by
  obtain ⟨G, hL, hR, hb, ha, hdL, hdR, _, _⟩ :=
    exists_seedGluedPair_retaining_logSlope hD hc hd TL TR hTL hTR K hq
  exact ⟨G, hL, hR, hb, ha, hdL, hdR⟩

/-- The original global-seed interface. The stronger construction also
records that every outward germ of the two pure tails is retained. -/
theorem exists_seedGluedPair {D : ReferenceData} {c d : ℝ} {uL uR : ℝ → ℝ}
    (hD : RadialProfileGeometry D) (hc : c ∈ radialCore D) (hd : d ∈ radialCore D)
    (TL : SeedPureTail D false c uL) (TR : SeedPureTail D true d uR)
    (hTL : TL.mode = 2) (hTR : TR.mode = -2)
    (K : SeedCentralCutoff) {q : ℝ} (hq : 0 < q) :
    Nonempty (SeedGluedPair D c d uL uR K q) := by
  obtain ⟨G, _, _, _, _, _, _⟩ := exists_seedGluedPair_retaining hD hc hd TL TR hTL hTR K hq
  exact ⟨G⟩

end ContinuousFlexibility.Radial
