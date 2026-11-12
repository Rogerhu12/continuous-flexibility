import ContinuousFlexibility.Statements.Nonlinear

/-!
# Uniqueness of canonical representations for N07b

The actual piecewise L² classes determine the canonical source. Injectivity
of the volume model's forget map then determines its source element.
For an unknown, the same physical field and left constant determine every
L² row; retaining the other two scalars determines the full unknown.

These statements use no additional regularity, coordinate estimates, or
membership in the fixed reference graph.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {V : VolumeModelData S K}

/-- Equality of the actual L² classes is coordinatewise a.e. equality. -/
theorem n07b_canonicalSequence_eq_of_ae {F G : CanonicalSequence S K}
    (h : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      (G m : PolarPoint → ℝ)) : F = G := by
  funext m
  exact Lp.ext (h m)

/-- A fixed physical source has at most one canonical source sequence. -/
theorem n07b_canonicalSource_unique {z : AnnularState S × ℝ}
    {f : PolarPoint → ℝ} {F G : CanonicalSequence S K}
    (hF : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f)
    (hG : ∀ m, (G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f) : F = G := by
  apply n07b_canonicalSequence_eq_of_ae
  intro m
  exact (hF m).trans (hG m).symm

/-- The forget map recovers a volume-level element from its a.e. source rows. -/
theorem n07b_volume_eq_of_ae (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {s : ℕ} {F G : V.level γ t s}
    (h : ∀ m, (V.forget γ t s F m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] (V.forget γ t s G m : PolarPoint → ℝ)) :
    F = G := by
  apply hV.2.2.1 γ t s
  exact n07b_canonicalSequence_eq_of_ae h

/-- Two volume-level realizations of the same actual canonical source agree. -/
theorem n07b_volume_eq_of_canonicalSource (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {s : ℕ} {z : AnnularState S × ℝ} {f : PolarPoint → ℝ}
    {F G : V.level γ t s}
    (hF : ∀ m, (V.forget γ t s F m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f)
    (hG : ∀ m, (V.forget γ t s G m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f) : F = G := by
  apply hV.2.2.1 γ t s
  exact n07b_canonicalSource_unique hF hG

/-- The source part of a representation is independent of its unknown and height. -/
theorem n07b_source_eq_of_representation {z : AnnularState S × ℝ}
    {U W : CanonicalUnknown S K} {F G : CanonicalSequence S K}
    {η ξ f : PolarPoint → ℝ}
    (hU : HasCanonicalRepresentation D S C K z U F η f)
    (hW : HasCanonicalRepresentation D S C K z W G ξ f) : F = G :=
  n07b_canonicalSource_unique hU.2 hW.2

/-- Source uniqueness also holds before applying the volume forget map. -/
theorem n07b_volume_eq_of_representation (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {s : ℕ} {z : AnnularState S × ℝ}
    {U W : CanonicalUnknown S K} {F G : V.level γ t s}
    {η ξ f : PolarPoint → ℝ}
    (hU : HasCanonicalRepresentation D S C K z U (V.forget γ t s F) η f)
    (hW : HasCanonicalRepresentation D S C K z W (V.forget γ t s G) ξ f) :
    F = G :=
  n07b_volume_eq_of_canonicalSource hV hU.2 hW.2

/-- The physical field and the left constant determine all canonical L² rows. -/
theorem n07b_rows_eq_of_representation {z : AnnularState S × ℝ}
    {U W : CanonicalUnknown S K} {F G : CanonicalSequence S K}
    {η f g : PolarPoint → ℝ}
    (hU : HasCanonicalRepresentation D S C K z U F η f)
    (hW : HasCanonicalRepresentation D S C K z W G η g)
    (hleft : U.2.1 = W.2.1) : U.1 = W.1 := by
  apply lp.ext
  funext m
  apply Lp.ext
  have hrow := hU.1 m
  rw [hleft] at hrow
  exact hrow.trans (hW.1 m).symm

/-- Full unknown uniqueness retains the three stored scalar coordinates. -/
theorem n07b_unknown_eq_of_representation {z : AnnularState S × ℝ}
    {U W : CanonicalUnknown S K} {F G : CanonicalSequence S K}
    {η f g : PolarPoint → ℝ}
    (hU : HasCanonicalRepresentation D S C K z U F η f)
    (hW : HasCanonicalRepresentation D S C K z W G η g)
    (hleft : U.2.1 = W.2.1)
    (hnu : U.2.2.1 = W.2.2.1)
    (hcompat : U.2.2.2 = W.2.2.2) : U = W :=
  Prod.ext (n07b_rows_eq_of_representation hU hW hleft)
    (Prod.ext hleft (Prod.ext hnu hcompat))

end ContinuousFlexibility.Analysis
