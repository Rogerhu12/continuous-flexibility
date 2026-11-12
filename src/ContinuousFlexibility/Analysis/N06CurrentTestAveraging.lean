import ContinuousFlexibility.Analysis.N06FullPeriodOperatorTests
import ContinuousFlexibility.Analysis.N06PhysicalRepresentativeUniqueness

/-!
# Actual current test averaging on the physical pieces

The two canonical source identities imply the physical averaging identity
by the true inverse-chart formula and the nonzero height/Jacobian factor.
Consequently the current operator sends a half-periodic physical test to
a half-periodic function on each actual physical piece. No periodicity or
global smoothness of the bare corrected coefficients is assumed.

The actual planar a.e. cover gives the identities for almost every radial
coordinate and almost every angle, exactly as required by the integrals.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- A source equality at the actual chart image is a physical equality:
the genuine height/Jacobian factor cannot vanish on an open piece. -/
theorem n06_current_source_eq_iff_on_piece
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K z m) :
    canonicalSource S K z m f (K.chart z m p) =
        canonicalSource S K z m g (K.chart z m p) ↔ f p = g p := by
  have hc := h04.1.charts z hz hs m
  let w : ℝ := K.height z m p / |planeJacobian (K.chart z m) p|
  have hw : w ≠ 0 := div_ne_zero (hc.2.2.2.2.2.2.2 p hp).1.ne'
    (abs_ne_zero.mpr (hc.2.2.2.2.2.2.2 p hp).2.1)
  have hsource (v : PolarPoint → ℝ) :
      canonicalSource S K z m v (K.chart z m p) = w * v p := by
    simp only [canonicalSource, hc.2.2.1 p hp, w]
    ring
  rw [hsource f, hsource g]
  constructor
  · exact mul_left_cancel₀ hw
  · intro h
    rw [h]

/-- The actual source averaging identities imply the physical identity
on both signs of the atlas, without an operator-periodicity hypothesis. -/
theorem n06_current_divergence_average_on_piece
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    n06_radialTestAverage (divergenceOperator (L.coefficients z) φ) p =
      divergenceOperator (L.coefficients z) (n06_radialTestAverage φ) p := by
  apply (n06_current_source_eq_iff_on_piece h04 hz hs hp).mp
  have hq := (h04.1.charts z hz hs m).1 hp
  cases hm : K.positive m
  · exact n06_negative_current_source_average hT hS h03 h04 hz hs hm hφ hq
  · exact n06_positive_current_source_average hT hS h01 h03 h04 hz hs m hm hφ.1 hq

/-- A half-periodic test has half-periodic actual operator output on
each physical piece. The conclusion is pointwise at every angle. -/
theorem n06_current_divergence_periodic_on_piece
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    (hπ : Function.Periodic φ (0, Real.pi))
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    divergenceOperator (L.coefficients z) φ (p + (0, Real.pi)) =
      divergenceOperator (L.coefficients z) φ p := by
  have havg : n06_radialTestAverage φ = φ := by
    funext q
    rw [n06_radialTestAverage_apply, hπ q]
    ring
  have he := n06_current_divergence_average_on_piece hT hS h01 h03 h04 hz hs hφ hp
  rw [havg, n06_radialTestAverage_apply] at he
  linarith

/-- A scalar-angle form for direct use in half/full angular integrals. -/
theorem n06_current_divergence_periodic_slice
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    (hπ : Function.Periodic φ (0, Real.pi))
    {r : ℝ} (hr : ∀ θ, (r, θ) ∈ physicalPieceOpen S K z m) :
    Function.Periodic (fun θ => divergenceOperator (L.coefficients z) φ (r, θ)) Real.pi := by
  intro θ
  simpa only [Prod.mk_add_mk, add_zero] using
    n06_current_divergence_periodic_on_piece hT hS h01 h03 h04 hz hs hφ hπ
      (hr θ)

/-- The actual planar cover gives the iterated almost-everywhere statement.
It does not assert an angle-independent exceptional set for moving cuts. -/
theorem n06_physicalPieces_radial_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {P : PolarPoint → Prop}
    (hP : ∀ m p, p ∈ physicalPieceOpen S K z m → P p) :
    ∀ᵐ r ∂volume.restrict (radialCore D), ∀ᵐ θ ∂volume, P (r, θ) := by
  have hmeasure : (volume : Measure PolarPoint).restrict (annularOpen D) =
      (volume.restrict (radialCore D)).prod volume := by
    change ((volume : Measure ℝ).prod volume).restrict
      (radialCore D ×ˢ (univ : Set ℝ)) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  apply Measure.ae_ae_of_ae_prod
  rw [← hmeasure]
  filter_upwards [n06_physical_piece_cover_ae h04 hz hs] with p hp
  obtain ⟨m, hm⟩ := hp
  exact hP m p hm

theorem n06_current_divergence_average_radial_ae
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    ∀ᵐ r ∂volume.restrict (radialCore D), ∀ᵐ θ ∂volume,
      n06_radialTestAverage (divergenceOperator (L.coefficients z) φ) (r, θ) =
        divergenceOperator (L.coefficients z) (n06_radialTestAverage φ) (r, θ) :=
  n06_physicalPieces_radial_ae h04 hz hs fun _ _ hp =>
    n06_current_divergence_average_on_piece hT hS h01 h03 h04 hz hs hφ hp

theorem n06_current_divergence_periodic_radial_ae
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    (hπ : Function.Periodic φ (0, Real.pi)) :
    ∀ᵐ r ∂volume.restrict (radialCore D), ∀ᵐ θ ∂volume,
      divergenceOperator (L.coefficients z) φ (r, θ + Real.pi) =
        divergenceOperator (L.coefficients z) φ (r, θ) := by
  have he := n06_physicalPieces_radial_ae h04 hz hs fun _ _ hp =>
    n06_current_divergence_periodic_on_piece hT hS h01 h03 h04 hz hs hφ hπ hp
  filter_upwards [he] with r hr
  filter_upwards [hr] with θ hθ
  simpa only [Prod.mk_add_mk, add_zero] using hθ

end ContinuousFlexibility.Statements
