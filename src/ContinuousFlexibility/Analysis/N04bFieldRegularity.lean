module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Raw corrected fields for the qualitative canonical construction

These conditions concern the actual coefficient functions of the corrected
divergence operator. They contain no chart, inverse chart, height gauge,
canonical density, transmission equation, or coordinate estimate.

The cumulative N01--N03 properties separately retain the actual root germs,
the corrected characteristic equation and exact returns, and the bilinear
source error. Spatial regularity of an arbitrary stored corrected field is
not inferred merely from regularity of the decoded source error.
-/

@[expose] public section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

/-- Spatial regularity and strict type of the actual corrected field on the
physical annulus. The positive radial coefficient is required on the entire
annulus; strict hyperbolicity is required throughout every negative component,
including the part outside the optical correction collars. -/
structure N04bFieldRegularity (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (base : ℕ) (ε : ℝ) : Prop where
  smooth_coefficients :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D) ∧
      ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D) ∧
      ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D)
  periodic_coefficients :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ r ∈ Ioo D.a D.b,
        Function.Periodic (fun θ => (L.coefficients z).a (r, θ)) Real.pi ∧
        Function.Periodic (fun θ => (L.coefficients z).b (r, θ)) Real.pi ∧
        Function.Periodic (fun θ => (L.coefficients z).c (r, θ)) Real.pi
  positive_a :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ p ∈ annularOpen D, 0 < (L.coefficients z).a p
  /-- The explicitly constructed correction is the actual radial optical flow
  at the reference state. This is a raw construction property, proved before
  introducing any canonical chart. -/
  reference_flow :
    ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      L.minusFlow (C.referenceState, 0) m r θ =
        θ - ∫ s in C.left m..r, Real.sqrt (-deriv D.w s / (s * D.w s))
  negative_discriminant :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m, ∀ p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
        0 < (L.coefficients z).b p ^ 2 -
          (L.coefficients z).a p * (L.coefficients z).c p

/-- The raw field properties imply the actual spatial correction contract. -/
theorem N04bFieldRegularity.toReturnCorrectionSpatialProperties
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hfield : N04bFieldRegularity D S C L base ε) :
    ReturnCorrectionSpatialProperties D S C L base ε := by
  intro z hz hs
  have hregular := hfield.smooth_coefficients z hz hs
  refine ⟨hregular.2.1, hregular.2.2, ?_⟩
  rintro ⟨r, θ⟩ hp
  have hperiod := hfield.periodic_coefficients z hz hs r hp.1
  simpa only [Prod.mk_add_mk, add_zero] using
    And.intro (hperiod.2.1 θ) (hperiod.2.2 θ)

/-- A genuine cumulative corrected field with the additional raw regularity
needed to construct its characteristic atlas. All witnesses may be chosen
together; no normal-form certificate is included in this statement. -/
def N04bFieldDataStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ base loss : ℕ, ∃ ε : ℝ,
        IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
          NonlinearPropertiesThrough03 A.val T S C R L base loss ε ∧
            N04bFieldRegularity A.val S C L base ε

end ContinuousFlexibility.Statements
