import ContinuousFlexibility.Radial.ConnectedReferenceBorder
import ContinuousFlexibility.Radial.CentralCompactColumnInverse

/-!
# The same reference geometry and its true central inverse

The actual metric-variation column is used throughout. Its normalized
pairing with the reference kernel determines the ordinary pairing with
the central model kernel, including the amplitude factor. This supplies
the nonorthogonality needed for the physical central inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

/-- Compact containment in the radial core changes the annular normalized
pairing into the same ordinary integral over the whole line. -/
theorem referenceColumn_integral_eq_one {D : ReferenceData}
    (hborder : RadialTrueBorder D)
    (hcore : tsupport (referenceColumn D) ⊆ radialCore D) :
    (∫ r : ℝ, referenceColumn D r * D.phi r) = 1 := by
  have hsupp : Function.support (fun r => referenceColumn D r * D.phi r) ⊆
      Ioc D.a D.b := by
    intro r hr
    have hnonzero : referenceColumn D r ≠ 0 := by
      intro hz
      apply hr
      change referenceColumn D r * D.phi r = 0
      rw [hz, zero_mul]
    have hi := hcore (subset_tsupport (referenceColumn D) hnonzero)
    change D.a < r ∧ r < D.b at hi
    exact ⟨hi.1, hi.2.le⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  exact hborder.2.2.2.1

/-- The normalization is with the actual reference kernel. On its central
patch that kernel is amplitude times the fixed central kernel. -/
theorem referenceColumn_centralKernel_pairing {D : ReferenceData}
    {l h amplitude : ℝ}
    (hborder : RadialTrueBorder D)
    (hcore : tsupport (referenceColumn D) ⊆ radialCore D)
    (hsupp : tsupport (referenceColumn D) ⊆ Ioo l h)
    (hamplitude : amplitude ≠ 0)
    (hmodel : EqOn D.phi (fun r => amplitude * centralKernelHeight r) (Ioo l h)) :
    (∫ r : ℝ, referenceColumn D r * centralKernelHeight r) = 1 / amplitude := by
  have heq : (fun r => referenceColumn D r * D.phi r) =
      fun r => amplitude * (referenceColumn D r * centralKernelHeight r) := by
    funext r
    change referenceColumn D r * D.phi r =
      amplitude * (referenceColumn D r * centralKernelHeight r)
    by_cases hr : r ∈ tsupport (referenceColumn D)
    · rw [hmodel (hsupp hr)]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hr]
      ring
  have hmul : amplitude * (∫ r : ℝ, referenceColumn D r * centralKernelHeight r) = 1 := by
    rw [← integral_const_mul, ← heq]
    exact referenceColumn_integral_eq_one hborder hcore
  apply (eq_div_iff hamplitude).mpr
  simpa only [mul_comm] using hmul

theorem referenceColumn_centralKernel_pairing_ne_zero {D : ReferenceData}
    {l h amplitude : ℝ}
    (hborder : RadialTrueBorder D)
    (hcore : tsupport (referenceColumn D) ⊆ radialCore D)
    (hsupp : tsupport (referenceColumn D) ⊆ Ioo l h)
    (hamplitude : amplitude ≠ 0)
    (hmodel : EqOn D.phi (fun r => amplitude * centralKernelHeight r) (Ioo l h)) :
    (∫ r : ℝ, referenceColumn D r * centralKernelHeight r) ≠ 0 := by
  rw [referenceColumn_centralKernel_pairing hborder hcore hsupp hamplitude hmodel]
  exact div_ne_zero one_ne_zero hamplitude

/-- A physical central inverse for this reference's actual column. The
profile and kernel identities tie its scale and amplitude to this same
central patch. Both inverse identities use the original distributional
equation and ordinary radial row. -/
def ReferenceCentralInverseRealization (D : ReferenceData) (l h : ℝ) : Prop :=
  ∃ scale amplitude : ℝ, ∃ hscale : 0 < scale,
    amplitude ≠ 0 ∧
    EqOn D.w (centralRadialProfile scale) (Ioo l h) ∧
    EqOn D.phi (fun r => amplitude * centralKernelHeight r) (Ioo l h) ∧
    ∃ (hg : ContDiff ℝ ∞ (referenceColumn D))
      (hc : HasCompactSupport (referenceColumn D))
      (hp : tsupport (referenceColumn D) ⊆ Ioi 0),
      (∫ r : ℝ, referenceColumn D r * centralKernelHeight r) = 1 / amplitude ∧
      ∃ C : ℝ, 0 < C ∧
        ∃ G : (CentralRadialHilbert scale × ℝ) →L[ℝ] (CentralRadialHilbert scale × ℝ),
          ‖G‖ ≤ C ∧
          (∀ F t, CentralCompactColumnEquation hscale hg hc hp F t
            (G (F, t)).1 (G (F, t)).2) ∧
          (∀ F t u c, CentralCompactColumnEquation hscale hg hc hp F t u c →
            G (F, t) = (u, c))

/-- Construct the inverse using the actual normalized column, with no
additional Hilbert pairing assumption. -/
theorem referenceCentralInverseRealization_of_model {D : ReferenceData}
    {l h scale amplitude : ℝ}
    (hborder : RadialTrueBorder D)
    (hcore : tsupport (referenceColumn D) ⊆ radialCore D)
    (hsupp : tsupport (referenceColumn D) ⊆ Ioo l h)
    (hscale : 0 < scale) (hamplitude : amplitude ≠ 0)
    (hwmodel : EqOn D.w (centralRadialProfile scale) (Ioo l h))
    (hφmodel : EqOn D.phi (fun r => amplitude * centralKernelHeight r) (Ioo l h))
    (hg : ContDiff ℝ ∞ (referenceColumn D))
    (hc : HasCompactSupport (referenceColumn D))
    (hp : tsupport (referenceColumn D) ⊆ Ioi 0) :
    ReferenceCentralInverseRealization D l h := by
  have hpair := referenceColumn_centralKernel_pairing hborder hcore hsupp hamplitude hφmodel
  have hpair_ne := referenceColumn_centralKernel_pairing_ne_zero
    hborder hcore hsupp hamplitude hφmodel
  refine ⟨scale, amplitude, hscale, hamplitude, hwmodel, hφmodel, hg, hc, hp, hpair, ?_⟩
  exact exists_centralCompactColumnInverse hscale hg hc hp hpair_ne

/-- Install the true border and obtain the central inverse on that very
same updated reference. Every profile and partition field remains the
one in the input data. -/
theorem exists_reference_central_inverse_controls {D : ReferenceData} {l h : ℝ}
    (hacc : IsAccumulatingProfile D) (hpatch : CentralPatch D l h) :
    ∃ χ : ℝ → ℝ,
      IsAccumulatingProfile (referenceWithTrueBorderControls D χ) ∧
      CentralPatch (referenceWithTrueBorderControls D χ) l h ∧
      RadialTrueBorder (referenceWithTrueBorderControls D χ) ∧
      tsupport χ ⊆ Ioo (centralRadius (sqrt centralOscillatorA)) h ∧
      tsupport (referenceColumn (referenceWithTrueBorderControls D χ)) ⊆
        Ioo (centralRadius (sqrt centralOscillatorA)) h ∧
      ReferenceCentralInverseRealization (referenceWithTrueBorderControls D χ) l h := by
  obtain ⟨χ, hacc', hpatch', hborder, hχcap, hg, hc, hcolumnCap⟩ :=
    exists_reference_true_border_controls hacc hpatch
  have hpatchData := hpatch'
  rcases hpatchData with ⟨hal, hlturn, _, hhb, scale, amplitude,
    hscale, hamplitude, hwmodel, hφmodel⟩
  have hlright : l < centralRadius (sqrt centralOscillatorA) :=
    hlturn.trans central_turning_radii_pos_ordered.2
  have hcore : tsupport (referenceColumn (referenceWithTrueBorderControls D χ)) ⊆
      radialCore (referenceWithTrueBorderControls D χ) := by
    intro r hr
    have hi := hcolumnCap hr
    exact ⟨hal.trans (hlright.trans hi.1), hi.2.trans hhb⟩
  have hcolumnPatch : tsupport (referenceColumn (referenceWithTrueBorderControls D χ)) ⊆
      Ioo l h := by
    intro r hr
    have hi := hcolumnCap hr
    exact ⟨hlright.trans hi.1, hi.2⟩
  have hpositive : tsupport (referenceColumn (referenceWithTrueBorderControls D χ)) ⊆
      Ioi 0 := by
    intro r hr
    exact (centralRadius_pos (sqrt centralOscillatorA)).trans (hcolumnCap hr).1
  exact ⟨χ, hacc', hpatch', hborder, hχcap, hcolumnCap,
    referenceCentralInverseRealization_of_model hborder hcore hcolumnPatch
      hscale hamplitude hwmodel hφmodel hg hc hpositive⟩

/-- The unchanged geometry fields and the physical inverse are returned
together, so a later construction can retain this single reference. -/
theorem exists_reference_central_inverse {D : ReferenceData} {l h : ℝ}
    (hacc : IsAccumulatingProfile D) (hpatch : CentralPatch D l h) :
    ∃ D' : ReferenceData,
      D'.a = D.a ∧ D'.b = D.b ∧ D'.w = D.w ∧ D'.phi = D.phi ∧
      D'.cells = D.cells ∧ D'.localizer = D.localizer ∧ D'.cellIndex = D.cellIndex ∧
      IsAccumulatingProfile D' ∧ CentralPatch D' l h ∧ RadialTrueBorder D' ∧
      tsupport (referenceColumn D') ⊆ Ioo (centralRadius (sqrt centralOscillatorA)) h ∧
      ReferenceCentralInverseRealization D' l h := by
  obtain ⟨χ, hacc', hpatch', hborder, _, hcap, hinverse⟩ :=
    exists_reference_central_inverse_controls hacc hpatch
  exact ⟨referenceWithTrueBorderControls D χ, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hacc', hpatch', hborder, hcap, hinverse⟩

/-- Every already realized joint geometry has the true central inverse
for its existing reference column. No second reference is chosen. -/
theorem ConnectedReferenceGeometry.centralInverseRealization
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes) :
    ReferenceCentralInverseRealization Γ.reference Γ.centralLeft Γ.centralRight := by
  rcases hΓ with ⟨_, _, hborder, _, hpatch, _, _, hg, hc, hcap⟩
  rcases hpatch with ⟨hal, hlturn, _, hhb, scale, amplitude,
    hscale, hamplitude, hwmodel, hφmodel⟩
  have hlright : Γ.centralLeft < centralRadius (sqrt centralOscillatorA) :=
    hlturn.trans central_turning_radii_pos_ordered.2
  have hcore : tsupport (referenceColumn Γ.reference) ⊆ radialCore Γ.reference := by
    intro r hr
    have hi := hcap hr
    exact ⟨hal.trans (hlright.trans hi.1), hi.2.trans hhb⟩
  have hpatchSupport : tsupport (referenceColumn Γ.reference) ⊆
      Ioo Γ.centralLeft Γ.centralRight := by
    intro r hr
    have hi := hcap hr
    exact ⟨hlright.trans hi.1, hi.2⟩
  have hpositive : tsupport (referenceColumn Γ.reference) ⊆ Ioi 0 := by
    intro r hr
    exact (centralRadius_pos (sqrt centralOscillatorA)).trans (hcap hr).1
  exact referenceCentralInverseRealization_of_model hborder hcore hpatchSupport
    hscale hamplitude hwmodel hφmodel hg hc hpositive

/-- One invocation of R08 supplies the selected tails, connected profile,
true border, and physical central inverse in the same joint witness. -/
theorem exists_connectedReferenceGeometry_central_inverse (hR08 : R08Statement)
    (requiredHead : ℝ) (hhead : 0 < requiredHead) :
    ∃ Γ : ConnectedReferenceGeometry,
      Γ.headLength = requiredHead ∧ Γ.Realizes ∧
      ReferenceCentralInverseRealization Γ.reference Γ.centralLeft Γ.centralRight := by
  obtain ⟨Γ, hlength, hΓ⟩ := exists_connectedReferenceGeometry hR08 requiredHead hhead
  exact ⟨Γ, hlength, hΓ, ConnectedReferenceGeometry.centralInverseRealization hΓ⟩

end ContinuousFlexibility.Radial
