import ContinuousFlexibility.Radial.SelectedRetainedPair
import ContinuousFlexibility.Radial.SeedFixedBorderGeometry

/-!
# The retained first cones and fixed border on one common reference

The selected sequence, desired first-cone length, central model window and
fixed border are all inputs. The theorem retains the actual pair used by
the construction and identifies the final reference functions with it.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem exists_seedRetainedFixedBorderGeometry (B : FixedCentralBorder)
    {S : SelectedTailData} (hS : IsSelectedTail S)
    (hentries : S.entry false S.chain.index < S.entry true S.chain.index)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hbridge : ∀ side r,
      r ∈ uIcc (S.cut side S.chain.index) (S.entry side S.chain.index) →
        0 < deriv (S.family S.sigma).w r)
    {T q length : ℝ} (hT : sqrt centralOscillatorA + 2 ≤ T)
    (hq : 0 < q) (hlength : 0 < length) :
    ∃ K : SeedCentralCutoff, ∃ P : SeedRetainedPair S K q length,
      ∃ Γ : ConnectedReferenceGeometry,
        Γ.selected = S ∧ Γ.headLength = q ∧ Γ.Realizes ∧
        Γ.reference.w = P.pair.profile ∧ Γ.reference.phi = P.pair.height ∧
        Γ.centralLeft = exp K.left ∧ Γ.centralRight = exp K.right ∧
        Γ.centralLeft < centralRadius (-T) ∧ centralRadius T < Γ.centralRight ∧
        referenceColumn Γ.reference = fixedCentralColumn B.chi ∧
        EqOn Γ.reference.w (centralRadialProfile 1)
          (Ioo Γ.centralLeft Γ.centralRight) ∧
        EqOn Γ.reference.phi centralKernelHeight
          (Ioo Γ.centralLeft Γ.centralRight) ∧ RadialConstructionGeometry Γ.reference := by
  obtain ⟨K, hleft, hright, _⟩ := exists_seedCentralCutoff_model_window T
  obtain ⟨P⟩ := exists_seedRetainedPair hS hband hbridge K hq hlength
  have hentry (right : Bool) :
      S.entry right S.chain.index ∈ radialCore (S.family S.sigma) :=
    (hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband).2.1
  obtain ⟨D, hconstruction, hDw, hDφ, hacc, hw, hφ, hkernel, hpatch, hheads, htails⟩ :=
    exists_seedControlledReference_with_construction hS hentries hentry hband K hq
      (P.toEntryPair hS hband)
  have hDw' : D.w = P.pair.profile := by
    simpa only [SeedRetainedPair.toEntryPair_profile] using hDw
  have hDφ' : D.phi = P.pair.height := by
    simpa only [SeedRetainedPair.toEntryPair_height] using hDφ
  have hleftcap : exp K.left < fixedCentralCapLeft := by
    change exp K.left < centralRadius (sqrt centralOscillatorA + 1)
    exact hleft.trans_le (strictMono_centralRadius.monotone
      (by linarith [sqrt_nonneg centralOscillatorA]))
  have hrightcap : fixedCentralCapRight < exp K.right := by
    change centralRadius (sqrt centralOscillatorA + 2) < exp K.right
    exact (strictMono_centralRadius.monotone hT).trans_lt hright
  have hcap : Ioo fixedCentralCapLeft fixedCentralCapRight ⊆
      Ioo (exp K.left) (exp K.right) :=
    fun _ hr => ⟨hleftcap.trans hr.1, hr.2.trans hrightcap⟩
  obtain ⟨hborder, hcol⟩ := B.install (hpatch.1.trans hleftcap)
    (hrightcap.trans hpatch.2.2.2.1)
    (fun _ hr => hw (hcap hr)) (fun _ hr => hφ (hcap hr))
  let D' := referenceWithTrueBorderControls D B.chi
  let Γ : ConnectedReferenceGeometry := ⟨S, D', exp K.left, exp K.right, q⟩
  have hreal : Γ.Realizes := by
    dsimp only [ConnectedReferenceGeometry.Realizes, Γ, D']
    refine ⟨hS, ?_, hborder, hkernel, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (referenceWithTrueBorderControls_accumulating_iff D B.chi).mpr hacc
    · exact (referenceWithTrueBorderControls_centralPatch_iff
        D B.chi (exp K.left) (exp K.right)).mpr hpatch
    · exact (connectedPositiveHeads_update_controls
        D B.chi (exp K.left) (exp K.right) q).mpr hheads
    · exact (connectedSelectedTails_update_controls
        S D B.chi (exp K.left) (exp K.right)).mpr htails
    · rw [hcol]
      exact B.column_smooth
    · rw [hcol]
      exact B.column_compact
    · rw [hcol]
      intro r hr
      have hi := B.column_support hr
      exact ⟨fixedCentralCap_order.2.1.trans hi.1, hi.2.trans hrightcap⟩
  exact ⟨K, P, Γ, rfl, rfl, hreal, hDw', hDφ', rfl, rfl, hleft, hright, hcol, hw, hφ, hconstruction⟩

/-- Nonvanishing of the actual profile locates the cap in the core; no
unrecorded inequality concerning the gluing radii is needed. -/
theorem radialCore_mem_of_profile_pos {D : ReferenceData}
    (hD : RadialProfileGeometry D) {r : ℝ} (hr : 0 < D.w r) : r ∈ radialCore D := by
  constructor
  · by_contra hh
    have hz := hD.2.2.1.2 r (Or.inl (le_of_not_gt hh))
    exact hr.ne' hz
  · by_contra hh
    have hz := hD.2.2.1.2 r (Or.inr (le_of_not_gt hh))
    exact hr.ne' hz

theorem SeedRetainedPair.reference_left_cone_germ {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length r : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile) (hr : 0 < r)
    (hc : r ∈ uIcc P.left.inner (S.cut false S.chain.index)) :
    D.w =ᶠ[𝓝 (P.pair.radiusL * r)]
      (fun t => (P.pair.heightL * P.left.coneScale) * t) := by
  rw [uIcc_of_ge P.left.inner_order.le] at hc
  rw [hw]
  exact (P.left_profile_germ hr hc.2).trans
    (radialRadiusScale_cone_germ P.pair.radiusL_pos.ne'
      (P.left.cone_germ r (by rwa [uIcc_of_ge P.left.inner_order.le])))

theorem SeedRetainedPair.reference_right_cone_germ {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length r : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile)
    (hc : r ∈ uIcc P.right.inner (S.cut true S.chain.index)) :
    D.w =ᶠ[𝓝 (P.pair.radiusR * r)]
      (fun t => (P.pair.heightR * P.right.coneScale) * t) := by
  rw [uIcc_of_le P.right.inner_order.le] at hc
  rw [hw]
  exact (P.right_profile_germ hc.1).trans
    (radialRadiusScale_cone_germ (P.pair.radiusL_pos.trans_le P.pair.radius_order).ne'
      (P.right.cone_germ r (by rwa [uIcc_of_le P.right.inner_order.le])))

end ContinuousFlexibility.Radial
