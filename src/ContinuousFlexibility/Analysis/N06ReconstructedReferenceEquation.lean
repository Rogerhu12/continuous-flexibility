module

public import ContinuousFlexibility.Analysis.N06PhysicalPairingCongruence
public import ContinuousFlexibility.Analysis.N06PhysicalSourceUniqueness

/-!
# The N05 reference equation on the explicit periodic reconstruction

This is the actual physical reference equation already defining the chosen
N05 graph. Its unknown and source may both be replaced by their explicit
canonical reconstructions because their periodic representatives agree
almost everywhere. The source-normalizing column is retained verbatim.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n06_reconstructed_reference_equation_of_representation
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S)
    (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {ηref fref : PolarPoint → ℝ} {γ M₀ M₁ : ℝ}
    (hrep : HasCanonicalRepresentation D S C K (C.referenceState, 0) U F ηref fref)
    (hweak : ReferenceGraph D γ M₀ M₁ (ηref, U.2.2.1)
      ((fun p => fref p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0)) :
    let η := n06PhysicalHeight K (C.referenceState, 0)
      (fun m => (U.1 m : PolarPoint → ℝ)) U.2.1
    let f := n06PhysicalSource K (C.referenceState, 0)
      (fun m => (F m : PolarPoint → ℝ))
    HasCanonicalRepresentation D S C K (C.referenceState, 0) U
      F η f ∧
    Function.Periodic η (0, Real.pi) ∧ Function.Periodic f (0, Real.pi) ∧
    referenceRow D η = 0 ∧
    ∀ φ, RadialTest D φ →
      radialWeakPairing D η φ + U.2.2.1 *
        (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          referenceColumn D r * Radial.cosineMode 2 θ * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (f (r, θ) - U.2.2.2 *
          (S.height (3 / 4 : ℝ)).decode S.psi (r, θ)) * φ (r, θ)) := by
  dsimp only
  obtain ⟨aL, haL⟩ := hweak.1
  have hηperiod : Function.Periodic ηref (0, Real.pi) := haL.2.2.1
  have hψperiod : Function.Periodic ((S.height (3 / 4 : ℝ)).decode S.psi)
      (0, Real.pi) := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.2.1
  have hfperiod : Function.Periodic fref (0, Real.pi) := by
    intro p
    have hred := hweak.2.1.2.2.1 p
    change fref (p + (0, Real.pi)) - U.2.2.2 *
        (S.height (3 / 4 : ℝ)).decode S.psi (p + (0, Real.pi)) =
      fref p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p at hred
    rw [hψperiod p] at hred
    exact sub_left_inj.mp hred
  have hηae := n06PhysicalHeight_ae_eq hN04 href hsector hrep hηperiod
  have hfae := n06PhysicalSource_ae_eq hN04 href hsector hrep hfperiod
  have hnamed := n06_physical_representation hN04 href hsector U
    F
  refine ⟨hnamed.1, hnamed.2, n06PhysicalSource_periodic hN04 href hsector _,
    (n06_referenceRow_congr_ae hab hηae).trans hweak.2.2.1, ?_⟩
  intro φ hφ
  have hηpair := n06_physicalPairing_congr_ae hab hηae
    (fun p => Radial.radialPDE D.w (fun r θ => φ (r, θ)) p.1 p.2)
  have hfpair := n06_physicalPairing_congr_ae hab
    (hfae.sub (Filter.EventuallyEq.refl _
      (fun p => U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p))) φ
  simp only [Pi.sub_apply] at hfpair
  unfold radialWeakPairing
  rw [hηpair, hfpair]
  exact hweak.2.2.2 φ hφ

theorem n06_reconstructed_reference_equation
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S)
    (hN04 : N04Properties D T S C L K base loss ε)
    (hN05 : N05Properties D T S C K V b B)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState) (u : B.Space) :
    let η := n06PhysicalHeight K (C.referenceState, 0)
      (fun m => (u.val.1.1 m : PolarPoint → ℝ)) u.val.1.2.1
    let f := n06PhysicalSource K (C.referenceState, 0)
      (fun m => (V.forget (3 / 4 : ℝ) 0 b u.val.2 m : PolarPoint → ℝ))
    HasCanonicalRepresentation D S C K (C.referenceState, 0) u.val.1
      (V.forget (3 / 4 : ℝ) 0 b u.val.2) η f ∧
    Function.Periodic η (0, Real.pi) ∧ Function.Periodic f (0, Real.pi) ∧
    referenceRow D η = 0 ∧
    ∀ φ, RadialTest D φ →
      radialWeakPairing D η φ + u.val.1.2.2.1 *
        (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          referenceColumn D r * Radial.cosineMode 2 θ * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (f (r, θ) - u.val.1.2.2.2 *
          (S.height (3 / 4 : ℝ)).decode S.psi (r, θ)) * φ (r, θ)) := by
  have hgraph := hN05.2.2.2.2.2.2.1
  obtain ⟨_, ηref, fref, hrep, hweak⟩ := (hgraph u.val).mp u.property
  exact n06_reconstructed_reference_equation_of_representation hab hS hN04 href hsector
    hrep hweak

end ContinuousFlexibility.Statements
