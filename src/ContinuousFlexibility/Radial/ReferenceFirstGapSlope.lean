module

public import ContinuousFlexibility.Radial.SelectedSideTransport
public import ContinuousFlexibility.Radial.CentralModelSlopeWindow

/-!
# One uniform profile-slope bound on the actual first gaps

The retained connectors and the fixed central model meet through full
profile germs.  The old cut-to-join cone then extends the same bound to
both physical matching joins, without choosing a new reference geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem SeedRetainedPair.reference_buffer_gap_logSlope {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length T : ℝ} (P : SeedRetainedPair S K q length)
    {Γ : ConnectedReferenceGeometry} (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (hT : 0 ≤ T) (hTL : Γ.centralLeft < centralRadius (-T))
    (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
      (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
    {r : ℝ} (hr : 0 < r)
    (hgap : r ∈ Icc (P.pair.radiusL * S.cut false S.chain.index) (centralRadius (-T)) ∪
      Icc (centralRadius T) (P.pair.radiusR * S.cut true S.chain.index)) :
    (3 / 4 : ℝ) * Γ.reference.w r ≤ r * deriv Γ.reference.w r := by
  have horder : centralRadius (-T) ≤ centralRadius T :=
    strictMono_centralRadius.monotone (by linarith only [hT])
  have hm (hi : r ∈ Ioo Γ.centralLeft Γ.centralRight)
      (ho : r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) :
      (3 / 4 : ℝ) * Γ.reference.w r ≤ r * deriv Γ.reference.w r := by
    have he : Γ.reference.w =ᶠ[𝓝 r] centralRadialProfile 1 :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds hi.1 hi.2) (fun _ ht => hmodel ht)
    apply logSlope_lower_of_germ he
    exact (le_div_iff₀ (centralRadialProfile_pos (by norm_num : (0 : ℝ) < 1) hr)).mp
      (hwindow r hr ho)
  rcases hgap with hL | hR
  · by_cases ho : r ≤ Γ.centralLeft
    · rw [hw]
      apply P.left_logSlope_lower r
      exact ⟨hL.1, by rwa [hleft] at ho⟩
    · exact hm ⟨lt_of_not_ge ho, hL.2.trans_lt (horder.trans_lt hTR)⟩ (Or.inl hL.2)
  · by_cases ho : Γ.centralRight ≤ r
    · rw [hw]
      apply P.right_logSlope_lower r
      exact ⟨by rwa [hright] at ho, hR.2⟩
    · exact hm ⟨hTL.trans_le (horder.trans hR.1), lt_of_not_ge ho⟩ (Or.inr hR.1)

/-- The original first cone is retained through both physical endpoint
germs, so its logarithmic profile slope remains exactly one. -/
theorem SeedRetainedPair.reference_first_join_logSlope {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (right : Bool)
    (hcone : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ uIcc (S.cut right S.chain.index)
      (S.joinInner right S.chain.index), (S.family S.sigma).w =ᶠ[𝓝 x] (fun t => C * t))
    {r : ℝ} (hr : 0 < r)
    (hcap : r ∈ uIcc (P.sideRadius right * S.cut right S.chain.index)
      (P.sideRadius right * S.joinInner right S.chain.index)) :
    (3 / 4 : ℝ) * D.w r ≤ r * deriv D.w r := by
  have hκ := P.sideRadius_pos right
  have hx : r / P.sideRadius right ∈ uIcc (S.cut right S.chain.index)
      (S.joinInner right S.chain.index) := (mem_uIcc_div_pos hκ).mpr hcap
  have hm := hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband
  have hc := hm.1
  have hp := hm.2.2.1
  have hxCore : r / P.sideRadius right ∈ radialCore (S.family S.sigma) :=
    ⟨(lt_min hc.1 hp.1).trans_le hx.1, hx.2.trans_lt (max_lt hc.2 hp.2)⟩
  have ho : if right then S.cut right S.chain.index ≤ r / P.sideRadius right
      else r / P.sideRadius right ≤ S.cut right S.chain.index := by
    have horder := hm.2.2.2.2.1
    cases right
    · rw [uIcc_of_ge horder.2.le] at hx
      exact hx.2
    · rw [uIcc_of_le horder.1.le] at hx
      exact hx.1
  obtain ⟨C, hC, hCg⟩ := hcone
  have hg := (P.reference_side_old_germ hw hS right hxCore ho).trans
    (radialRadiusScale_cone_germ hκ.ne' (hCg _ hx))
  have he : P.sideRadius right * (r / P.sideRadius right) = r := by
    field_simp [hκ.ne'] <;> ring
  rw [he] at hg
  apply logSlope_lower_of_germ hg
  change (3 / 4 : ℝ) * ((P.sideHeight right * C) * r) ≤
    r * deriv (fun t : ℝ => (P.sideHeight right * C) * t) r
  have hd : HasDerivAt (fun t : ℝ => (P.sideHeight right * C) * t)
      (P.sideHeight right * C) r := by
    simpa only [mul_one] using (hasDerivAt_id' r).const_mul (P.sideHeight right * C)
  rw [hd.deriv]
  nlinarith [mul_pos (mul_pos (P.sideHeight_pos right) hC) hr]

/-- The bound holds on both complete first gaps, from the selected
matching joins to the already fixed central buffer. -/
theorem SeedRetainedPair.reference_first_gaps_logSlope {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length T : ℝ} (P : SeedRetainedPair S K q length)
    {Γ : ConnectedReferenceGeometry} (hw : Γ.reference.w = P.pair.profile)
    (hS : IsSelectedTail S) (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hcone : ∀ right, ∃ C : ℝ, 0 < C ∧ ∀ x ∈ uIcc (S.cut right S.chain.index)
      (S.joinInner right S.chain.index), (S.family S.sigma).w =ᶠ[𝓝 x] (fun t => C * t))
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (hT : 0 ≤ T) (hTL : Γ.centralLeft < centralRadius (-T))
    (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
      (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
    {r : ℝ} (hr : 0 < r)
    (hgap : r ∈ Icc (P.pair.radiusL * S.joinInner false S.chain.index) (centralRadius (-T)) ∪
      Icc (centralRadius T) (P.pair.radiusR * S.joinInner true S.chain.index)) :
    (3 / 4 : ℝ) * Γ.reference.w r ≤ r * deriv Γ.reference.w r := by
  have hcore := P.reference_buffer_gap_logSlope hw hleft hright hT hTL hTR hmodel hwindow hr
  rcases hgap with hL | hR
  · by_cases hc : P.pair.radiusL * S.cut false S.chain.index ≤ r
    · exact hcore (Or.inl ⟨hc, hL.2⟩)
    · apply P.reference_first_join_logSlope hw hS hband false (hcone false) hr
      exact ⟨(min_le_right _ _).trans hL.1,
        (lt_of_not_ge hc).le.trans (le_max_left _ _)⟩
  · by_cases hc : r ≤ P.pair.radiusR * S.cut true S.chain.index
    · exact hcore (Or.inr ⟨hR.1, hc⟩)
    · apply P.reference_first_join_logSlope hw hS hband true (hcone true) hr
      exact ⟨(min_le_left _ _).trans (lt_of_not_ge hc).le,
        hR.2.trans (le_max_right _ _)⟩

end ContinuousFlexibility.Radial
