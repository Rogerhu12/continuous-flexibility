module

public import ContinuousFlexibility.Radial.R07FirstBandMatching

/-!
# Retained geometry of the actual first-band matching

After the product heights have been selected, the original natural
solutions at the two first entries determine a finite collection of
nonzero states. A fixed positive middle with two cone heads avoids all
their determinant zeros. The outgoing functions are unchanged on the
tails, and the short-head-join estimate proves the angle inequality for
the actual cut-normalized incoming solutions. The full chosen cone specification,
its cross-cut order, and its actual profile germs are retained for R10a.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

private theorem r10aFirst_range_height_bounds {lo hi W z amp : ℝ}
    (hlo : 0 < lo) (hamp : 0 < amp)
    (hW : lo ≤ W ∧ W ≤ hi) (hz : lo ≤ z ∧ z ≤ hi) :
    0 < amp * z ∧ amp * z ≤ (hi / lo) * (amp * W) ∧
      amp * W ≤ (hi / lo) * (amp * z) := by
  have hhi : 0 < hi := hlo.trans_le (hW.1.trans hW.2)
  have hC : 0 ≤ hi / lo := (div_pos hhi hlo).le
  have he : hi / lo * lo = hi := div_mul_cancel₀ _ hlo.ne'
  have hZW : z ≤ hi / lo * W := by
    calc
      z ≤ hi := hz.2
      _ = hi / lo * lo := he.symm
      _ ≤ hi / lo * W := mul_le_mul_of_nonneg_left hW.1 hC
  have hWZ : W ≤ hi / lo * z := by
    calc
      W ≤ hi := hW.2
      _ = hi / lo * lo := he.symm
      _ ≤ hi / lo * z := mul_le_mul_of_nonneg_left hz.1 hC
  refine ⟨mul_pos hamp (hlo.trans_le hz.1), ?_, ?_⟩
  · simpa only [mul_left_comm amp, mul_assoc] using mul_le_mul_of_nonneg_left hZW hamp.le
  · simpa only [mul_left_comm amp, mul_assoc] using mul_le_mul_of_nonneg_left hWZ hamp.le

private theorem r10aFirst_cauchy_reduced_state_ne_zero {e J : ℝ} {v : ℝ → ℝ}
    (he : e ≠ 0) (hJ : J ≠ 0) (hv : (v e, deriv v e) ≠ (0, 0)) :
    (v e, e * deriv v e / J - v e) ≠ (0, 0) := by
  intro hz
  have h₀ : v e = 0 := congrArg Prod.fst hz
  have h₁ : e * deriv v e / J - v e = 0 := congrArg Prod.snd hz
  rw [h₀, sub_zero] at h₁
  have hp : e * deriv v e = 0 := by
    have hm := congrArg (fun x : ℝ => x * J) h₁
    simpa only [div_mul_cancel₀ _ hJ, zero_mul] using hm
  exact hv (Prod.ext h₀ ((mul_eq_zero.mp hp).resolve_left he))

/-- A replacement middle and actual first-band solutions, with the exact
matching geometry and angle required by the final assembly. -/
theorem exists_r10a_first_band_matching_data {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ)
    (hPhi : ContDiff ℝ ∞ phi ∧ (∀ x, x ≤ 1 ∨ G.rightEnd ≤ x → phi x = 0) ∧
      ∃ x ∈ Ioo 1 G.rightEnd, phi x ≠ 0)
    (sigma : ℕ → ℝ) (hsigma : ∀ n, 1 ≤ sigma n ∧ sigma n ≤ 2)
    {constants : ℕ → ℝ}
    (hreal : MorseChainRealization T sigma (morseChainReferenceFamily G phi sigma) constants)
    (Cstar : ℝ) (V : Bool → ℕ → ℝ → ℝ)
    (hV : ∀ side j, 2 ≤ j → Even j → radialFrequencyBand T Cstar T.index j →
      ContDiff ℝ ∞ (V side j) ∧
        RadialNaturalTail (morseChainReferenceFamily G phi sigma) side j
          (r07CellEntry T side T.index) (V side j)) :
    ∃ (H : R07ConeMiddleData) (cFirst : ℝ) (U : Bool → ℕ → ℝ → ℝ),
      R07MiddleAdmissible G H.middle ∧ 0 < cFirst ∧ cFirst ≤ 1 / 48 ∧
      H.cut false < H.cut true ∧
      (∀ side, ∃ scale : ℝ, 0 < scale ∧
        ∀ x ∈ uIcc (H.cut side) (H.join side),
          (r07MiddleReferenceFamily G H.middle phi sigma).w =ᶠ[𝓝 x]
            fun r => scale * r) ∧
      (∃ WL WR eta : ℝ, 0 < eta ∧
        R07ConeMiddleSpecification (morseChainCellRightRadius T false 0)
          (morseChainCellLeftRadius T true 0) WL WR eta (morseChainMiddleUnit G) H) ∧
      ∀ side j, 2 ≤ j → Even j → radialFrequencyBand T Cstar T.index j →
        let D := r07MiddleReferenceFamily G H.middle phi sigma
        ContDiff ℝ ∞ (U side j) ∧
          R07MatchingGeometry T D side T.index j (H.cut side) (H.join side)
            (r07CellEntry T side T.index) (U side j) (V side j) ∧
          cFirst * exp (-(T.index : ℝ) ^ 2) ≤
            radialAngleSine
              (radialState D j (r07CellEntry T side T.index) (D.w (H.join side)) (U side j))
              (radialState D j (r07CellEntry T side T.index) (D.w (H.join side)) (V side j)) := by
  classical
  let a := morseChainCellRightRadius T false 0
  let b := morseChainCellLeftRadius T true 0
  let f := morseChainMiddleUnit G
  let old := morseChainReferenceFamily G phi sigma
  let entry := fun side => r07CellEntry T side T.index
  have heq (side : Bool) : entry side = if side then b else a := by
    cases side <;> simp only [entry, r07CellEntry, a, b, morseChainCellRightRadius,
      morseChainCellLeftRadius, Nat.add_zero, Bool.false_eq_true, ite_false, ite_true]
  have hEntry (side : Bool) : entry side ∈ radialCore old := by
    apply hreal.radius_mem_core side T.index le_rfl
    have ho := (hreal.2.2.1 side T.index le_rfl).2.1.le
    cases side
    · exact ⟨ho, le_rfl⟩
    · exact ⟨le_rfl, ho⟩
  have haCore : a ∈ radialCore old := by
    simpa only [heq, ite_false, Bool.false_eq_true] using hEntry false
  have hbCore : b ∈ radialCore old := by simpa only [heq, ite_true] using hEntry true
  have ha : 0 < a := hreal.geometry.1.trans haCore.1
  have hab : a < b := by
    simpa only [a, b, morseChainCellRightRadius, morseChainCellLeftRadius, Nat.add_zero] using G.middle_gap
  have hf : R07MiddleAdmissible G f := r07MiddleUnit_admissible G
  let B : Bool → R07FirstFrequency T Cstar → ℝ × ℝ := fun side i =>
    (V side i.1 (entry side), entry side * deriv (V side i.1) (entry side) / (i.1 : ℝ) ^ 2 -
      V side i.1 (entry side))
  have hB (side : Bool) (i : R07FirstFrequency T Cstar) : B side i ≠ (0, 0) := by
    have hv := hV side i.1 i.2.1 i.2.2.1 i.2.2.2
    have hj : (0 : ℝ) < i.1 := by exact_mod_cast (by have := i.2.1; omega : 0 < i.1)
    exact r10aFirst_cauchy_reduced_state_ne_zero (hreal.geometry.1.trans (hEntry side).1).ne'
      (pow_ne_zero 2 hj.ne')
      (radialNaturalTail_cauchyData_ne_zero hreal.geometry (hEntry side) hv.1 hv.2)
  obtain ⟨WL, WR, δ, eta, H, hWL, hW, hWR, hδ, hδ48, heta, hH, hangle, haction⟩ :=
    exists_r07_finite_cone_choice (fun i : R07FirstFrequency T Cstar => i.1) (fun i => i.2.1)
      B hB ha hab hf.1 hf.2.1 hf.2.2.2.2
  have hSpecification := hH
  rcases hH with ⟨hHs, hHp, hHa, hHb, hHd, hajL, hjLcL, hcLcR, hcRjR, hjRb,
    hshortL, hshortR, hScale, hCone, hWLvalue, hWRvalue⟩
  have hM : R07MiddleAdmissible G H.middle :=
    ⟨hHs, hHp, hHa.trans hf.2.2.1, hHb.trans hf.2.2.2.1, hHd⟩
  let D := r07MiddleReferenceFamily G H.middle phi sigma
  let amp := morseChainAmplitude T sigma T.index
  let contrast := f b / f a
  have hamp : 0 < amp := morseChainAmplitude_pos T sigma hsigma T.index
  have hD : RadialProfileGeometry D := by
    change RadialProfileGeometry (r07MiddleReferenceFamily G H.middle phi sigma)
    rw [r07MiddleReferenceFamily_admissible G H.middle phi sigma hsigma]
    exact r07MiddlePatchedProfile_geometry G hM sigma hsigma phi 0 0 hPhi
  have hInside (x : ℝ) (hx : x ∈ Icc a b) : D.w =ᶠ[𝓝 x] fun r => amp * H.middle r := by
    change (r07MiddleReferenceFamily G H.middle phi sigma).w =ᶠ[𝓝 x]
      fun r => amp * H.middle r
    rw [r07MiddleReferenceFamily_admissible G H.middle phi sigma hsigma]
    exact (r07MiddlePatchedProfile_germs G hM sigma hsigma).2 x hx
  have hCore (x : ℝ) (hx : x ∈ Icc a b) : x ∈ radialCore D :=
    ⟨haCore.1.trans_le hx.1, hx.2.trans_lt hbCore.2⟩
  have hcut (side : Bool) : H.cut side ∈ Icc a b := by
    cases side
    · exact ⟨(hajL.trans hjLcL).le, (hcLcR.trans (hcRjR.trans hjRb)).le⟩
    · exact ⟨(hajL.trans (hjLcL.trans hcLcR)).le, (hcRjR.trans hjRb).le⟩
  have hjoin (side : Bool) : H.join side ∈ Icc a b := by
    cases side
    · exact ⟨hajL.le, (hjLcL.trans (hcLcR.trans (hcRjR.trans hjRb))).le⟩
    · exact ⟨(hajL.trans (hjLcL.trans (hcLcR.trans hcRjR))).le, hjRb.le⟩
  have hentry (side : Bool) : entry side ∈ Icc a b := by
    rw [heq]
    cases side
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  have horder (side : Bool) : if side then H.cut side < H.join side ∧ H.join side < entry side
      else entry side < H.join side ∧ H.join side < H.cut side := by
    rw [heq]
    cases side
    · exact ⟨hajL, hjLcL⟩
    · exact ⟨hcRjR, hjRb⟩
  have hmono : MonotoneOn H.middle (Icc a b) :=
    (strictMonoOn_of_deriv_pos (convex_Icc a b) hHs.continuous.continuousOn
      (fun x hx => hHd x (interior_subset hx))).monotoneOn
  have hrange (x : ℝ) (hx : x ∈ Icc a b) : f a ≤ H.middle x ∧ H.middle x ≤ f b := by
    constructor
    · calc
        f a = H.middle a := hHa.eq_of_nhds.symm
        _ ≤ H.middle x := hmono ⟨le_rfl, hab.le⟩ hx hx.1
    · calc
        H.middle x ≤ H.middle b := hmono hx ⟨hab.le, le_rfl⟩ hx.2
        _ = f b := hHb.eq_of_nhds
  have hcontrast : 1 ≤ contrast := (le_div_iff₀ (hf.2.1 a)).mpr (by
    simpa only [one_mul] using (hrange a ⟨le_rfl, hab.le⟩).1.trans (hrange a ⟨le_rfl, hab.le⟩).2)
  have hweight (side : Bool) (x : ℝ) (hx : x ∈ uIcc (H.join side) (entry side)) :
      0 < D.w x ∧ D.w x ≤ contrast * D.w (H.join side) ∧
        D.w (H.join side) ≤ contrast * D.w x := by
    have hxMid := ordConnected_Icc.uIcc_subset (hjoin side) (hentry side) hx
    rw [(hInside x hxMid).eq_of_nhds, (hInside (H.join side) (hjoin side)).eq_of_nhds]
    exact r10aFirst_range_height_bounds (hf.2.1 a) hamp (hrange _ (hjoin side)) (hrange x hxMid)
  have hcone (side : Bool) (x : ℝ) (hx : x ∈ uIcc (H.cut side) (H.join side)) :
      D.w =ᶠ[𝓝 x] fun r => (amp * H.scale side) * r := by
    have hxMid := ordConnected_Icc.uIcc_subset (hcut side) (hjoin side) hx
    filter_upwards [hInside x hxMid, hCone side x hx] with y hy hyCone
    rw [hy, hyCone, mul_assoc]
  have hEntryHeight (side : Bool) : D.w (entry side) = amp * (if side then f b else f a) := by
    rw [(hInside (entry side) (hentry side)).eq_of_nhds]
    cases side
    · simp only [heq, Bool.false_eq_true, ite_false, hHa.eq_of_nhds]
    · simp only [heq, ite_true, hHb.eq_of_nhds]
  have hJoinHeight (side : Bool) : D.w (H.join side) = amp * (if side then WR else WL) := by
    rw [(hInside (H.join side) (hjoin side)).eq_of_nhds]
    cases side
    · simp only [Bool.false_eq_true, ite_false, hWLvalue]
    · simp only [ite_true, hWRvalue]
  have hstates (side : Bool) (i : R07FirstFrequency T Cstar) :
      radialState D i.1 (entry side) (D.w (H.join side)) (V side i.1) =
        ((B side i).1, (if side then f b else f a) / (if side then WR else WL) * (B side i).2) := by
    unfold radialState
    rw [hEntryHeight, hJoinHeight, mul_div_mul_left _ _ hamp.ne']
  have hlen (side : Bool) : |entry side - H.join side| ≤ eta := by
    rw [heq]
    cases side
    · simp only [Bool.false_eq_true, ite_false]
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hajL)]
      exact hshortL.le
    · simp only [ite_true]
      rw [abs_of_pos (sub_pos.mpr hjRb)]
      exact hshortR.le
  have hex : ∀ q : Bool × R07FirstFrequency T Cstar, ∃ u : ℝ → ℝ,
      ContDiff ℝ ∞ u ∧
      R07MatchingGeometry T D q.1 T.index q.2.1 (H.cut q.1) (H.join q.1) (entry q.1) u (V q.1 q.2.1) ∧
      δ ≤ radialAngleSine (radialState D q.2.1 (entry q.1) (D.w (H.join q.1)) u)
        (radialState D q.2.1 (entry q.1) (D.w (H.join q.1)) (V q.1 q.2.1)) := by
    rintro ⟨side, i⟩
    have hsmall : 2 * (i.1 : ℝ) ^ 2 * contrast / min (H.join side) (entry side) *
        |entry side - H.join side| ≤ δ / 12 := by
      have hmin : a ≤ min (H.join side) (entry side) := le_min (hjoin side).1 (hentry side).1
      have hminpos : 0 < min (H.join side) (entry side) := ha.trans_le hmin
      have hcontrast₀ : 0 ≤ contrast := zero_le_one.trans hcontrast
      calc
        _ ≤ 2 * (i.1 : ℝ) ^ 2 * contrast / min (H.join side) (entry side) * eta :=
          mul_le_mul_of_nonneg_left (hlen side) (by positivity)
        _ ≤ _ := haction i _ hmin
    have hideal : 2 * δ ≤ radialAngleSine (1, r07ConeSlope side i.1)
        (radialState D i.1 (entry side) (D.w (H.join side)) (V side i.1)) := by
      rw [hstates]
      exact hangle side i
    obtain ⟨u, hu, hu₀, hu₁, _, hueq, hwd, hangleU⟩ :=
      exists_r07_cone_incoming_angle hD i.2.1 (hCore _ (hcut side)) (hCore _ (hjoin side))
        (hCore _ (hentry side)) (horder side) (mul_pos hamp (hScale side)) (hcone side)
        hcontrast (hweight side) hδ hδ48 hsmall hideal
    refine ⟨u, hu, ?_, hangleU⟩
    refine ⟨hCore _ (hcut side), hCore _ (hentry side), hCore _ (hjoin side),
      hD.2.2.2.2.1 _ (hCore _ (hjoin side)), horder side, rfl, ?_, hwd,
      hu.contDiffAt, hu.contDiffAt, ⟨hu.contDiffOn, hueq⟩, ?_⟩
    · rw [if_pos rfl]
      exact ⟨⟨amp * H.scale side, mul_pos hamp (hScale side), hcone side _ left_mem_uIcc⟩, hu₀, hu₁⟩
    · exact (r07MiddleReferenceFamily_natural_entry_iff G hM phi sigma hsigma side le_rfl i.1
        (V side i.1)).mpr (hV side i.1 i.2.1 i.2.2.1 i.2.2.2).2
  choose U hU using hex
  let incoming : Bool → ℕ → ℝ → ℝ := fun side j =>
    if hj : 2 ≤ j ∧ Even j ∧ radialFrequencyBand T Cstar T.index j then U (side, ⟨j, hj⟩)
    else fun _ => 0
  refine ⟨H, δ, incoming, hM, hδ, hδ48, hcLcR,
    (fun side => ⟨amp * H.scale side, mul_pos hamp (hScale side), hcone side⟩),
    ⟨WL, WR, eta, heta, hSpecification⟩, ?_⟩
  intro side j hj heven hband
  have hjvalid : 2 ≤ j ∧ Even j ∧ radialFrequencyBand T Cstar T.index j :=
    ⟨hj, heven, hband⟩
  have hi := hU (side, ⟨j, hjvalid⟩)
  have hmargin : δ * exp (-(T.index : ℝ) ^ 2) ≤ δ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (T.index : ℝ)))) hδ.le
  simpa only [incoming, dite_eq_left hjvalid, D, entry] using
    And.intro hi.1 (And.intro hi.2.1 (hmargin.trans hi.2.2))

end ContinuousFlexibility.Radial
