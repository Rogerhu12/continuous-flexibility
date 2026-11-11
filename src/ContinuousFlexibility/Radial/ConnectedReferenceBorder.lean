import ContinuousFlexibility.Radial.ReferenceTrueBorder

/-!
# Retaining the connected selected geometry when installing its true border

R08 supplies the selected tail and the connected reference in one witness.
This file keeps that witness intact, including the positive cone heads and
the actual radius/height transport on each tail. Installing the metric
control changes none of those geometric data.

This is the initial common geometry for terminal matching. It does not
assert an inner or outer inverse, a selected matching margin, or a choice
of quantitative parameters that the R08 statement does not supply.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- The two actual positive cone heads appearing in the R08 conclusion. -/
def ConnectedPositiveHeads (D : ReferenceData) (l h requiredHead : ℝ) : Prop :=
  ∃ l₁ l₂ h₁ h₂ cL cR : ℝ,
    D.a < l₁ ∧ l₁ < l₂ ∧ l₂ < l ∧ h < h₁ ∧ h₁ < h₂ ∧ h₂ < D.b ∧
    0 < cL ∧ 0 < cR ∧ log (l₂ / l₁) ≥ requiredHead ∧
    log (h₂ / h₁) ≥ requiredHead ∧
    (∀ r ∈ Ioo l₁ l₂, D.w r = cL * r) ∧
    (∀ r ∈ Ioo h₁ h₂, D.w r = cR * r) ∧
    (∀ r ∈ Ioo l₂ l, 0 < deriv D.w r) ∧
    (∀ r ∈ Ioo h h₁, 0 < deriv D.w r)

/-- The actual tail equalities and unchanged negative-component travel
integrals, with one orientation parameter for both ends. -/
def ConnectedSelectedTails (S : SelectedTailData) (D : ReferenceData) (l h : ℝ) : Prop :=
  ∀ right : Bool, ∃ radiusScale heightScale amplitude : ℝ,
    0 < radiusScale ∧ 0 < heightScale ∧ amplitude ≠ 0 ∧
    (if right then D.b = radiusScale * (S.family S.sigma).b
     else D.a = radiusScale * (S.family S.sigma).a) ∧
    (∀ r ∈ radialTailInterval (S.family S.sigma) right
      (S.entry right S.chain.index),
      radiusScale * r ∈ radialTailInterval D right (if right then h else l) ∧
      D.w (radiusScale * r) = heightScale * radiusScale * (S.family S.sigma).w r ∧
      D.phi (radiusScale * r) = amplitude * S.outgoing right 2 r) ∧
    (∀ l₁ h₁, NegativeRadialComponent (S.family S.sigma) l₁ h₁ →
      Ioo l₁ h₁ ⊆ radialTailInterval (S.family S.sigma) right
        (S.entry right S.chain.index) →
      NegativeRadialComponent D (radiusScale * l₁) (radiusScale * h₁) ∧
        radialTravel D (radiusScale * l₁) (radiusScale * h₁) =
          radialTravel (S.family S.sigma) l₁ h₁)

/-- Pure geometric data. All of its properties are stated separately. -/
structure ConnectedReferenceGeometry where
  selected : SelectedTailData
  reference : ReferenceData
  centralLeft : ℝ
  centralRight : ℝ
  headLength : ℝ

def ConnectedReferenceGeometry.Realizes (Γ : ConnectedReferenceGeometry) : Prop :=
  IsSelectedTail Γ.selected ∧ IsAccumulatingProfile Γ.reference ∧
    RadialTrueBorder Γ.reference ∧
    (∀ r ∈ radialCore Γ.reference,
      radialJacobi 4 Γ.reference.w Γ.reference.phi r = 0) ∧
    CentralPatch Γ.reference Γ.centralLeft Γ.centralRight ∧
    ConnectedPositiveHeads Γ.reference Γ.centralLeft Γ.centralRight Γ.headLength ∧
    ConnectedSelectedTails Γ.selected Γ.reference Γ.centralLeft Γ.centralRight ∧
    ContDiff ℝ ∞ (referenceColumn Γ.reference) ∧
    HasCompactSupport (referenceColumn Γ.reference) ∧
    tsupport (referenceColumn Γ.reference) ⊆
      Ioo (centralRadius (sqrt centralOscillatorA)) Γ.centralRight

theorem connectedPositiveHeads_update_controls (D : ReferenceData) (χ : ℝ → ℝ)
    (l h requiredHead : ℝ) :
    ConnectedPositiveHeads (referenceWithTrueBorderControls D χ) l h requiredHead ↔
      ConnectedPositiveHeads D l h requiredHead := Iff.rfl

theorem connectedSelectedTails_update_controls (S : SelectedTailData)
    (D : ReferenceData) (χ : ℝ → ℝ) (l h : ℝ) :
    ConnectedSelectedTails S (referenceWithTrueBorderControls D χ) l h ↔
      ConnectedSelectedTails S D l h := Iff.rfl

/-- The selected tail, connected kernel, cells, and cone heads all belong
to one reference, now with the genuine normalized metric border. -/
theorem exists_connectedReferenceGeometry (hR08 : R08Statement)
    (requiredHead : ℝ) (hhead : 0 < requiredHead) :
    ∃ Γ : ConnectedReferenceGeometry,
      Γ.headLength = requiredHead ∧ Γ.Realizes := by
  obtain ⟨S, hS, D, hacc, hkernel, l, h, hpatch, hheads, htails⟩ :=
    hR08 requiredHead hhead
  obtain ⟨χ, hacc', hpatch', hborder, _, hgsmooth, hgcompact, hgcap⟩ :=
    exists_reference_true_border_controls hacc hpatch
  refine ⟨⟨S, referenceWithTrueBorderControls D χ, l, h, requiredHead⟩, rfl,
    hS, hacc', hborder, ?_, hpatch', ?_, ?_, hgsmooth, hgcompact, hgcap⟩
  · exact hkernel
  · exact (connectedPositiveHeads_update_controls D χ l h requiredHead).mpr hheads
  · exact (connectedSelectedTails_update_controls S D χ l h).mpr htails

end ContinuousFlexibility.Radial
