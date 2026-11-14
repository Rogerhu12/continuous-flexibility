module

public import ContinuousFlexibility.Radial.SeedControlledReference
public import ContinuousFlexibility.Radial.FixedCentralBorder

/-!
# One controlled reference with the preselected central border

The fixed border and model window are inputs.  The construction retains the
specified selected tail, both requested cone heads, and the entire model
window.  Its actual physical column is globally the already fixed column.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem exists_seedFixedBorderGeometry (B : FixedCentralBorder)
    {S : SelectedTailData} (hS : IsSelectedTail S)
    (hentries : S.entry false S.chain.index < S.entry true S.chain.index)
    (hentry : ∀ right,
      S.entry right S.chain.index ∈ radialCore (S.family S.sigma) ∧
      0 < deriv (S.family S.sigma).w (S.entry right S.chain.index) ∧
      RadialNaturalTail (S.family S.sigma) right 2
        (S.entry right S.chain.index) (S.outgoing right 2))
    {T q : ℝ} (hT : sqrt centralOscillatorA + 2 ≤ T) (hq : 0 < q) :
    ∃ Γ : ConnectedReferenceGeometry,
      Γ.selected = S ∧ Γ.headLength = q ∧ Γ.Realizes ∧
      Γ.centralLeft < centralRadius (-T) ∧ centralRadius T < Γ.centralRight ∧
      referenceColumn Γ.reference = fixedCentralColumn B.chi ∧
      EqOn Γ.reference.w (centralRadialProfile 1)
        (Ioo Γ.centralLeft Γ.centralRight) ∧
      EqOn Γ.reference.phi centralKernelHeight
        (Ioo Γ.centralLeft Γ.centralRight) := by
  obtain ⟨K, hleft, hright, _⟩ := exists_seedCentralCutoff_model_window T
  obtain ⟨D, hacc, hw, hφ, hkernel, hpatch, hheads, htails⟩ :=
    exists_seedControlledReference hS hentries hentry K hq
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
  have hwcap : EqOn D.w (centralRadialProfile 1)
      (Ioo fixedCentralCapLeft fixedCentralCapRight) := fun _ hr => hw (hcap hr)
  have hφcap : EqOn D.phi centralKernelHeight
      (Ioo fixedCentralCapLeft fixedCentralCapRight) := fun _ hr => hφ (hcap hr)
  obtain ⟨hborder, hcol⟩ := B.install (hpatch.1.trans hleftcap)
    (hrightcap.trans hpatch.2.2.2.1) hwcap hφcap
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
  exact ⟨Γ, rfl, rfl, hreal, hleft, hright, hcol, hw, hφ⟩

end ContinuousFlexibility.Radial
