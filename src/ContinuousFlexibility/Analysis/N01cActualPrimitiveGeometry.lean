import ContinuousFlexibility.Analysis.N01cScaledMorseOpticalCover
import ContinuousFlexibility.Analysis.N01cFiniteHeadOpticalBounds
import ContinuousFlexibility.Radial.R11aRetainedFamily
import ContinuousFlexibility.Radial.SeedCentralReturn

/-!
# Primitive optical geometry of the actual retained reference

The two tails use the quantitative Morse bound and their actual dilations.
The single central component uses its simple zeros and compactness. All
negative points are classified by the same glued profile, and the actual
cell pullback supplies the labels used by the uniform lower bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- The same reference retained by R11a has primitive optical geometry.
Every input is already retained by its concrete geometry factory. -/
theorem SeedRetainedPair.n01c_radialPrimitiveGeometry
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (Γ : ConnectedReferenceGeometry)
    (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hlarge : 100 ≤ S.chain.index) (hq : 0 < q) (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hconstruction : RadialConstructionGeometry Γ.reference)
    (hcoordinates : R11aRetainedCoordinates P Γ) :
    N01RadialPrimitiveGeometry Γ.reference := by
  let G := P.toEntryPair hS hband
  have hGL : G.radiusL = P.pair.radiusL := rfl
  have hGR : G.radiusR = P.pair.radiusR := rfl
  have hGw : G.profile = P.pair.profile := rfl
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hGeo : RadialProfileGeometry Γ.reference := (Classical.choose_spec hΓ.2.1).1
  have hentry (side : Bool) :
      S.entry side S.chain.index ∈ radialCore (S.family S.sigma) :=
    (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.1
  have hseam (side : Bool) :
      S.entry side S.chain.index = morseChainSeam S.chain side S.chain.index := by
    simpa only [morseChainSeam] using
      (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.2.1
  obtain ⟨e, N, _, hlabels, hindex, hcells, _, hleft, hright, _, ha, hb⟩ := hcoordinates
  have hindex' (m : ℕ) :
      Γ.reference.cellIndex m = max ((S.family S.sigma).cellIndex m) N := by
    simp only [hindex, hlabels]
  obtain ⟨κ, hκ, hoptical⟩ := hreal.exists_opticalRatio_radialE_lower_bound
  let R : Bool → ℝ := fun side => if side then G.radiusR else G.radiusL
  let H : Bool → ℝ := fun side => if side then G.heightR else G.heightL
  have hR (side : Bool) : 0 < R side := by
    cases side
    · exact G.radiusL_pos
    · exact G.radiusL_pos.trans_le G.radius_order
  have hH (side : Bool) : 0 < H side := by
    cases side
    · exact G.heightL_pos
    · exact G.heightR_pos
  have hprofile (side : Bool) (s : ℝ)
      (hs : s ∈ radialTailInterval (S.family S.sigma) side (S.entry side S.chain.index)) :
      Γ.reference.w (R side * s) = H side * R side * (S.family S.sigma).w s := by
    rw [hw]
    cases side
    · exact (G.left_tail s hs).1
    · exact (G.right_tail s hs).1
  have hcore (side : Bool) (s : ℝ)
      (hs : s ∈ radialTailInterval (S.family S.sigma) side (S.entry side S.chain.index)) :
      R side * s ∈ radialCore Γ.reference := by
    apply radialCore_mem_of_profile_pos hGeo
    rw [hprofile side s hs]
    apply mul_pos (mul_pos (hH side) (hR side))
    apply hreal.geometry.2.2.2.2.1
    cases side
    · exact ⟨hs.1, hs.2.trans (hentry false).2⟩
    · exact ⟨(hentry true).1.trans hs.1, hs.2⟩
  have htailCells (side : Bool) (m : ℕ) (s : ℝ)
      (hs : s ∈ radialTailInterval (S.family S.sigma) side (S.entry side S.chain.index))
      (hm : s ∈ (S.family S.sigma).cells m) : R side * s ∈ Γ.reference.cells m := by
    apply hcells m
    change e (R side * s) ∈ (S.family S.sigma).cells m
    cases side
    · change e (P.pair.radiusL * s) ∈ (S.family S.sigma).cells m
      rw [← hleft s hs.2.le, e.apply_symm_apply]
      exact hm
    · change e (P.pair.radiusR * s) ∈ (S.family S.sigma).cells m
      rw [← hright s hs.1.le, e.apply_symm_apply]
      exact hm
  have htail (side : Bool) (s : ℝ)
      (hs : s ∈ radialTailInterval (S.family S.sigma) side (S.entry side S.chain.index))
      (hsneg : deriv (S.family S.sigma).w s < 0) :
      N01cOpticalModelAt Γ.reference (κ⁻¹ / R side ^ 3) κ (R side * s) := by
    apply n01c_scaledMorse_opticalModelAt hreal hS.2.2.1 hlarge side le_rfl
      (hR side) (hH side) hκ hGeo
      (by simpa only [← hseam side] using hcore side)
      (by simpa only [← hseam side] using hprofile side)
      (by simpa only [← hseam side] using htailCells side)
      hindex' hoptical (by simpa only [← hseam side] using hs) hsneg
  let l := centralRadius (-sqrt centralOscillatorA)
  let u := centralRadius (sqrt centralOscillatorA)
  have hcentral : NegativeRadialComponent Γ.reference l u := by
    simpa only [NegativeRadialComponent, l, u, ha, hb, hw, hGL, hGR, hGw] using
      (G.central_model_return hq (hentry false) (hentry true)).1
  obtain ⟨c₀, hc₀, hcentralLower⟩ :=
    negativeRadialComponent_optical_lower_bound hGeo hcentral
  obtain ⟨_, _, hmargin⟩ := hconstruction.2.2
  obtain ⟨_, m, hhost, _⟩ := hmargin l u hcentral
  let c : ℝ := min c₀ (min (κ⁻¹ / R false ^ 3) (κ⁻¹ / R true ^ 3))
  have hc : 0 < c := lt_min hc₀
    (lt_min (div_pos (inv_pos.mpr hκ) (pow_pos (hR false) _))
      (div_pos (inv_pos.mpr hκ) (pow_pos (hR true) _)))
  apply n01c_radialPrimitiveGeometry_of_opticalPointCover hΓ.2.1
    (fun _ hr => (hΓ.2.2.1.2.2.1 hr).1) hc hκ.le
  intro r hr hneg
  have hrG : r ∈ Ioo (G.radiusL * (S.family S.sigma).a)
      (G.radiusR * (S.family S.sigma).b) := by
    simpa only [radialCore, Set.mem_Ioo, ha, hb, hGL, hGR] using hr
  have hnegG : deriv G.profile r < 0 := by simpa only [hw, hGw] using hneg
  rcases G.negative_deriv_cases hq hrG hnegG with hleftCase | hmiddle | hrightCase
  · obtain ⟨s, hs, rfl, hsneg⟩ := hleftCase
    exact (htail false s hs hsneg).mono_constant
      ((min_le_right _ _).trans (min_le_left _ _))
  · obtain ⟨hrMiddle, hnegCentral⟩ := hmiddle
    have hrpos : 0 < r := (exp_pos K.left).trans hrMiddle.1
    have hx : centralModelCoordinate r ^ 2 < centralOscillatorA := by
      apply (centralRadialProfile_deriv_neg_iff (by norm_num : (0 : ℝ) < 1) _).mp
      rw [centralRadius_modelCoordinate hrpos]
      exact hnegCentral
    have hxI := sq_lt.mp hx
    have hrI : r ∈ Ioo l u :=
      ⟨(strictMono_centralRadius hxI.1).trans_eq (centralRadius_modelCoordinate hrpos),
        (centralRadius_modelCoordinate hrpos).symm.trans_lt (strictMono_centralRadius hxI.2)⟩
    refine ⟨l, u, Γ.reference.cellIndex m, hcentral, hrI, ⟨m, rfl, hhost hrI⟩,
      fun t ht => ?_⟩
    have hweight : radialE (Γ.reference.cellIndex m) ^ (-κ) ≤ 1 :=
      rpow_le_one_of_one_le_of_nonpos
        (one_le_exp_iff.mpr ((sq_nonneg (Γ.reference.cellIndex m : ℝ)).trans
          (radial_nat_sq_le_Q _)))
        (neg_nonpos.mpr hκ.le)
    have hδ : 0 ≤ min (t - l) (u - t) :=
      le_min (sub_nonneg.mpr ht.1.le) (sub_nonneg.mpr ht.2.le)
    have hcoeff : c * radialE (Γ.reference.cellIndex m) ^ (-κ) ≤ c₀ := by
      calc
        c * radialE (Γ.reference.cellIndex m) ^ (-κ) ≤ c := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hweight hc.le
        _ ≤ c₀ := min_le_left _ _
    exact (mul_le_mul_of_nonneg_right hcoeff hδ).trans
      (hcentralLower t (Ioo_subset_Icc_self ht))
  · obtain ⟨s, hs, rfl, hsneg⟩ := hrightCase
    exact (htail true s hs hsneg).mono_constant
      ((min_le_right _ _).trans (min_le_right _ _))

end ContinuousFlexibility.Radial
