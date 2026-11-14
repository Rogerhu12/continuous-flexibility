module

public import ContinuousFlexibility.Analysis.N06PhysicalRepresentativeUniqueness
public import ContinuousFlexibility.Analysis.N06PhysicalPeriodicity

/-!
# Almost-everywhere uniqueness of the actual physical source

The source transform includes both the height and the chart Jacobian.
Their actual periodicity and nonvanishing make this transform injective
on periodic physical representatives, first on each piece and then on
the whole a.e. piece cover.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n06_canonicalSource_periodic_slice
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) {y : ℝ}
    (hy : y ∈ Ioo (K.left m) (K.right m)) :
    Function.Periodic (fun θ => canonicalSource S K z m f (y, θ)) Real.pi := by
  intro θ
  have hp : (y, θ) ∈ canonicalOpen S K m := ⟨hy, mem_univ _⟩
  have hc := hN04.1.charts z hz hs m
  have hpI := hc.2.1 hp
  have hh := (hc.2.2.2.2.2.2.2 _ hpI).2.2.2
  have hj := n06_planeJacobian_currentChart_lift hN04 hz hs m hpI
  have hlift : K.inverseChart z m (y, θ + Real.pi) =
      K.inverseChart z m (y, θ) + (0, Real.pi) := by
    simpa only [Prod.mk_add_mk, add_zero] using
      n06_inverseChart_lift hN04 hz hs m hp
  change K.height z m (K.inverseChart z m (y, θ + Real.pi)) *
      f (K.inverseChart z m (y, θ + Real.pi)) /
      |planeJacobian (K.chart z m) (K.inverseChart z m (y, θ + Real.pi))| = _
  rw [hlift, hh, hf, hj]
  rfl

theorem n06_canonicalSource_ae_injective_piece
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {f g : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (hg : Function.Periodic g (0, Real.pi))
    (heq : canonicalSource S K z m f =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m g) :
    f =ᵐ[volume.restrict (physicalPieceOpen S K z m)] g := by
  have hall := n06_periodic_ae_eq_on_strip
    (fun y hy => n06_canonicalSource_periodic_slice hN04 hz hs m hf hy)
    (fun y hy => n06_canonicalSource_periodic_slice hN04 hz hs m hg hy) heq
  have hphysical := n06_canonical_ae_pullback hN04 hz hs m hall
  have hc := hN04.1.charts z hz hs m
  filter_upwards [hphysical,
    ae_restrict_mem (hN04.1.domains z hz hs m).1.measurableSet] with p hp hpU
  have hleft := hc.2.2.1 p hpU
  have hh := (hc.2.2.2.2.2.2.2 p hpU).1.ne'
  have hj := abs_ne_zero.mpr (hc.2.2.2.2.2.2.2 p hpU).2.1
  change K.height z m (K.inverseChart z m (K.chart z m p)) *
      f (K.inverseChart z m (K.chart z m p)) /
      |planeJacobian (K.chart z m) (K.inverseChart z m (K.chart z m p))| =
    K.height z m (K.inverseChart z m (K.chart z m p)) *
      g (K.inverseChart z m (K.chart z m p)) /
      |planeJacobian (K.chart z m) (K.inverseChart z m (K.chart z m p))| at hp
  rw [hleft] at hp
  exact (mul_right_inj' hh).mp ((div_left_inj' hj).mp hp)

theorem n06_physical_ae_eq_of_pieces
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f g : PolarPoint → ℝ}
    (heq : ∀ m, f =ᵐ[volume.restrict (physicalPieceOpen S K z m)] g) :
    f =ᵐ[volume.restrict (annularOpen D)] g := by
  have hall : ∀ᵐ p ∂volume, ∀ m, p ∈ physicalPieceOpen S K z m → f p = g p := by
    apply ae_all_iff.mpr
    intro m
    exact (ae_restrict_iff' (hN04.1.domains z hz hs m).1.measurableSet).mp (heq m)
  have hall' : ∀ᵐ p ∂volume.restrict (annularOpen D),
      ∀ m, p ∈ physicalPieceOpen S K z m → f p = g p :=
    hall.filter_mono ae_restrict_le
  filter_upwards [hall', n06_physical_piece_cover_ae hN04 hz hs] with p hp hcover
  obtain ⟨m, hm⟩ := hcover
  exact hp m hm

theorem n06_canonicalSource_ae_injective
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f g : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (hg : Function.Periodic g (0, Real.pi))
    (heq : ∀ m, canonicalSource S K z m f =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m g) : f =ᵐ[volume.restrict (annularOpen D)] g :=
  n06_physical_ae_eq_of_pieces hN04 hz hs
    (fun m => n06_canonicalSource_ae_injective_piece hN04 hz hs m hf hg (heq m))

/-- The named source reconstructed from the original canonical L² source
equals any periodic physical source representing it. -/
theorem n06PhysicalSource_ae_eq
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {U : CanonicalUnknown S K}
    {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (hf : Function.Periodic f (0, Real.pi)) :
    n06PhysicalSource K z (fun m => (F m : PolarPoint → ℝ)) =ᵐ[
      volume.restrict (annularOpen D)] f := by
  have hnamed := (n06_physical_representation hN04 hz hs U F).1.2
  exact n06_canonicalSource_ae_injective hN04 hz hs
    (n06PhysicalSource_periodic hN04 hz hs _) hf
    (fun m => (hnamed m).symm.trans (hrep.2 m))

end ContinuousFlexibility.Statements
