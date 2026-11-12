import ContinuousFlexibility.Analysis.N06PeriodicNormalizedRepresentation
import ContinuousFlexibility.Analysis.N06PhysicalPeriodicity

/-!
# The weak equation of the actual named current representatives

The original perturbed relation allows existential physical
representatives. For the norm-limit argument we use the actual periodic
reconstruction, whose normalization is already supplied by the original
N05 graph. Proving its weak equation therefore implies the original
perturbed relation without changing that relation's definition.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ}

def N06NamedPhysicalWeakRelation (D : ReferenceData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (B : CanonicalDomainData S K V b) (z : AnnularState S × ℝ)
    (u : B.Space) (F : V.level (3 / 4 : ℝ) 0 b) : Prop :=
  let η := n06PhysicalHeight K z (fun m => (u.val.1.1 m : PolarPoint → ℝ)) u.val.1.2.1
  let f := n06PhysicalSource K z
    (fun m => (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ))
  ∀ φ, RadialTest D φ →
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      η (r, θ) * divergenceOperator (L.coefficients z) φ (r, θ))) +
      u.val.1.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C z (r, θ) * φ (r, θ))) +
      u.val.1.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) =
    ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))

/-- The original N05 graph supplies the normalization of the named
current representative, so its actual weak equation suffices for the
unchanged existential physical relation. -/
theorem n06_namedPhysicalWeakRelation_implies
    {D : ReferenceData} {T : MaterialData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b}
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (u : B.Space) (F : V.level (3 / 4 : ℝ) 0 b)
    (hweak : N06NamedPhysicalWeakRelation D C L B z u F) :
    PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b F) := by
  obtain ⟨hrep, hperiod, hrow⟩ := n06_graph_periodic_normalized_representation
    hab h04 h05 href hsector hz hs u (V.forget (3 / 4 : ℝ) 0 b F)
  exact ⟨_, _, hrep, hperiod, n06PhysicalSource_periodic h04 hz hs _, hrow, hweak⟩

end ContinuousFlexibility.Statements
