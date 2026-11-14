module

public import ContinuousFlexibility.Analysis.N01cFullNeighborhood
public import ContinuousFlexibility.Analysis.N01cHeightGeometry
public import ContinuousFlexibility.Scalar.TypeCorrection

/-!
# Spatial coefficient regularity and the exact characteristic type

N01a supplies smoothness of the actual controlled profile and of the actual
integral height.  N01b supplies the positive denominators on its full
neighbourhood.  Together they imply spatial smoothness of all three actual
coefficients throughout the open annulus.

The characteristic square-root argument is positive precisely where the
derivative of the perturbed profile is negative.  We therefore prove
smoothness of the actual minus speed on that domain.  No assertion that
every reference negative component retains its type is inserted: such a
claim needs the additional relative control estimate from the geometric
neighbourhood construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The relative logarithmic-control estimate used in the geometric
neighbourhood construction preserves the true derivative sign. -/
theorem deriv_logPerturbation_neg_of_relative_bound
    {w f : ℝ → ℝ} {r wr fr : ℝ}
    (hw : HasDerivAt w wr r) (hf : HasDerivAt f fr r)
    (hwr : wr < 0) (hsmall : |w r * fr| ≤ -wr / 2) :
    deriv (fun s => w s * Real.exp (f s)) r < 0 := by
  rw [deriv_fun_mul hw.differentiableAt hf.exp.differentiableAt,
    hw.deriv, hf.exp.deriv]
  have hsum : wr + w r * fr < 0 := by
    have hu := le_abs_self (w r * fr)
    linarith
  calc
    wr * Real.exp (f r) + w r * (Real.exp (f r) * fr) =
        (wr + w r * fr) * Real.exp (f r) := by ring
    _ < 0 := mul_neg_of_neg_of_pos hsum (Real.exp_pos _)

/-- The three original coefficient fields are spatially smooth at every
interior point, for every state in the full N01b neighbourhood. -/
theorem n01_originalCoefficients_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).a p ∧
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).b p ∧
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).c p := by
  obtain ⟨K, hK⟩ := hA.1.1
  have hden := n01PartB_denominators_pos hK.1 hS hA.2.1 hB hz hp
  have hr : 0 < p.1 := hK.1.1.trans hp.1.1
  have hcoeff := contDiffAt_heightLinearCoefficients
    (contDiff_stateProfile_of_partA hS hT hA z.1).contDiffAt
    (contDiff_stateHeight hS hT hA z).contDiffAt hr.ne' hden.2.2 hden.2.1.ne'
  exact ⟨hcoeff.1, hcoeff.2.1, hcoeff.2.2.2.1⟩

theorem n01_originalCoefficients_contDiffOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) ∧
    ContDiffOn ℝ ∞ (originalCoefficients D S C z).b (annularOpen D) ∧
    ContDiffOn ℝ ∞ (originalCoefficients D S C z).c (annularOpen D) := by
  exact ⟨fun p hp => (n01_originalCoefficients_contDiffAt hS hT hA hB hz hp).1.contDiffWithinAt,
    fun p hp => (n01_originalCoefficients_contDiffAt hS hT hA hB hz hp).2.1.contDiffWithinAt,
    fun p hp => (n01_originalCoefficients_contDiffAt hS hT hA hB hz hp).2.2.contDiffWithinAt⟩

/-- The square-root argument in the actual characteristic speed is positive
if and only if the perturbed profile has negative derivative. -/
theorem n01_characteristicDiscriminant_pos_iff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ↔
      deriv (stateProfile D S C z.1) p.1 < 0 := by
  obtain ⟨K, hK⟩ := hA.1.1
  have hden := n01PartB_denominators_pos hK.1 hS hA.2.1 hB hz hp
  have hr : 0 < p.1 := hK.1.1.trans hp.1.1
  have hneg := polar_corrected_determinant_neg_iff (stateHeight D S C z)
    ((contDiff_stateProfile_of_partA hS hT hA z.1).differentiable (by simp) p.1)
    hr hden.1 hden.2.2 hden.2.1.ne'
  change 0 < polarLinearB (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2 -
      polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p *
        polarCorrectedC (stateProfile D S C z.1) (stateHeight D S C z) p ↔ _
  constructor
  · intro h
    exact hneg.mp (by linarith)
  · intro h
    have hh := hneg.mpr h
    linarith

/-- Actual spatial smoothness of the minus characteristic speed at every
point of negative perturbed type. -/
theorem n01_minusCharacteristicSpeed_contDiffAt_of_profile_deriv_neg
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hneg : deriv (stateProfile D S C z.1) p.1 < 0) :
    ContDiffAt ℝ ∞ (minusCharacteristicSpeed (originalCoefficients D S C z)) p := by
  obtain ⟨K, hK⟩ := hA.1.1
  have hcoeff := n01_originalCoefficients_contDiffAt hS hT hA hB hz hp
  have ha := n01PartB_originalCoefficients_a_pos hK.1 hS hA.2.1 hB hz hp
  have hdisc := (n01_characteristicDiscriminant_pos_iff hS hT hA hB hz hp).mpr hneg
  exact (hcoeff.2.1.div hcoeff.1 ha.ne').sub
    ((((hcoeff.2.1.pow 2).sub (hcoeff.1.mul hcoeff.2.2)).sqrt hdisc.ne').div
      hcoeff.1 ha.ne')

/-- The exact negative-type domain of the perturbed profile is a smooth
domain for the actual minus characteristic speed. -/
theorem n01_minusCharacteristicSpeed_contDiffOn_negative
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    ContDiffOn ℝ ∞ (minusCharacteristicSpeed (originalCoefficients D S C z))
      {p | p ∈ annularOpen D ∧ deriv (stateProfile D S C z.1) p.1 < 0} :=
  fun _ hp =>
    (n01_minusCharacteristicSpeed_contDiffAt_of_profile_deriv_neg hS hT hA hB hz
      hp.1 hp.2).contDiffWithinAt

/-- When the geometric type-preservation estimate is available, it gives
the spatial-smoothness part of the speed input on the whole component. -/
theorem n01_minusCharacteristicSpeed_contDiffOn_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) (m : ℕ)
    (hneg : ∀ r ∈ Ioo (C.left m) (C.right m), deriv (stateProfile D S C z.1) r < 0) :
    ContDiffOn ℝ ∞ (minusCharacteristicSpeed (originalCoefficients D S C z))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  intro p hp
  have hinterval := hA.2.2.1.1 m
  have hp' : p ∈ annularOpen D :=
    ⟨⟨hinterval.1.trans hp.1.1, hp.1.2.trans hinterval.2.2⟩, mem_univ _⟩
  exact (n01_minusCharacteristicSpeed_contDiffAt_of_profile_deriv_neg
    hS hT hA hB hz hp' (hneg p.1 hp.1)).contDiffWithinAt

end ContinuousFlexibility.Statements
