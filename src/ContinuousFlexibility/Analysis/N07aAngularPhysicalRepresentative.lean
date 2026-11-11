import ContinuousFlexibility.Analysis.N07aAngularPullbackJets

/-!
# The same rough representatives on the actual physical pieces

These functions are obtained from the actual canonical representative by
the actual chart and gauge.  Their a.e. values are identified with the
original height remainder and source in `HasCanonicalRepresentation`.
Their physical angular jets are L² by the preceding true pullback result.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

def n07aPhysicalHeightRepresentative {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (v : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  K.height z m p * v (K.chart z m p)

def n07aPhysicalSourceRepresentative {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (v : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  |planeJacobian (K.chart z m) p| * ((K.height z m p)⁻¹ * v (K.chart z m p))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07aPhysicalHeightRepresentative_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v) :
    n07aPhysicalHeightRepresentative K z m v =ᵐ[
        canonicalMeasure S (n07aPhysicalIntervalData K) m]
      fun p => η p - U.2.1 * S.chiLeft p.1 := by
  have he := n07a_chart_ae_pullback h04 hz hs m (hv.symm.trans (hrep.1 m))
  obtain ⟨_, _, _, hpoint⟩ := n07a_physicalHalfGeometry h04 hz hs m
  filter_upwards [he, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)]
    with p hp hpQ
  have hd := hpoint p hpQ
  simp only [n07aPhysicalHeightRepresentative, hp, canonicalHeight, hd.1]
  field_simp [hd.2.1]

theorem n07aPhysicalSourceRepresentative_ae
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v) :
    n07aPhysicalSourceRepresentative K z m v =ᵐ[
      canonicalMeasure S (n07aPhysicalIntervalData K) m] f := by
  have he := n07a_chart_ae_pullback h04 hz hs m (hv.symm.trans (hrep.2 m))
  obtain ⟨_, _, _, hpoint⟩ := n07a_physicalHalfGeometry h04 hz hs m
  filter_upwards [he, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)]
    with p hp hpQ
  have hd := hpoint p hpQ
  simp only [n07aPhysicalSourceRepresentative, hp, canonicalSource, hd.1]
  field_simp [hd.2.1, abs_ne_zero.mpr hd.2.2]

theorem n07aPhysicalHeightRepresentative_contDiffOn
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m)) :
    ContDiffOn ℝ ∞ (n07aPhysicalHeightRepresentative K z m v) (physicalPieceOpen S K m) := by
  obtain ⟨hmap, _, _, _, hchart, _, hh, _⟩ := h04.2.2.2.2.2.2.2.1 z hz hs m
  exact hh.mul (hv.comp hchart hmap)

theorem n07aPhysicalHeightRepresentative_periodic_on
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {v : PolarPoint → ℝ} (hv : Function.Periodic v (0, Real.pi)) :
    ∀ p ∈ physicalPieceOpen S K m,
      n07aPhysicalHeightRepresentative K z m v (p + (0, Real.pi)) =
        n07aPhysicalHeightRepresentative K z m v p := by
  intro p hp
  have h := h04.2.2.2.2.2.2.2.1 z hz hs m |>.2.2.2.2.2.2.2 p hp
  simp only [n07aPhysicalHeightRepresentative, h.2.2.1, h.2.2.2, hv _]

theorem n07aPhysicalHeightRepresentative_even_on
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : ∀ p ∈ canonicalOpen S K m, v (p.1, -p.2) = v p) :
    ∀ p ∈ physicalPieceOpen S K m,
      n07aPhysicalHeightRepresentative K z m v (p.1, -p.2) =
        n07aPhysicalHeightRepresentative K z m v p := by
  intro p hp
  have href := h04.2.2.2.2.2.2.2.2.2.1 z hz hs m p hp
  have hmap := (h04.2.2.2.2.2.2.2.1 z hz hs m).1 hp
  simp only [n07aPhysicalHeightRepresentative, href.1, href.2.1, hv _ hmap]

theorem n07aPhysicalHeightRepresentative_angular_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m))
    (hLp : ∀ a b, MemLp (mixedDerivative a b v) 2 (canonicalMeasure S K m)) (n : ℕ) :
    MemLp (mixedDerivative 0 n
      (n07aPhysicalHeightRepresentative K (liftSectorParameter S C z) m v)) 2
      (canonicalMeasure S (n07aPhysicalIntervalData K) m) := by
  have hm := (h04.2.2.2.1 m).1
  obtain ⟨hmap, _, _, _, hchart, _⟩ := h04.2.2.2.2.2.2.2.1 _ hz' hs m
  exact n07a_angularJet_memLp_mul
    (n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 2)
    (hv.comp hchart hmap) n
    (fun j _ => n07a_current_chart_angular_memLp h04 href hcur z hz hz' hs m hv hLp j)

theorem n07aPhysicalSourceRepresentative_contDiffOn
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m)) :
    ContDiffOn ℝ ∞ (n07aPhysicalSourceRepresentative K (liftSectorParameter S C z) m v)
      (physicalPieceOpen S K m) := by
  have hm := (h04.2.2.2.1 m).1
  obtain ⟨hmap, _, _, _, hchart, _⟩ := h04.2.2.2.2.2.2.2.1 _ hz' hs m
  exact (n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 4).smooth.mul
    ((n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 3).smooth.mul
      (hv.comp hchart hmap))

theorem n07aPhysicalSourceRepresentative_angular_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m))
    (hLp : ∀ a b, MemLp (mixedDerivative a b v) 2 (canonicalMeasure S K m)) (n : ℕ) :
    MemLp (mixedDerivative 0 n
      (n07aPhysicalSourceRepresentative K (liftSectorParameter S C z) m v)) 2
      (canonicalMeasure S (n07aPhysicalIntervalData K) m) := by
  have hm := (h04.2.2.2.1 m).1
  obtain ⟨hmap, _, _, _, hchart, _⟩ := h04.2.2.2.2.2.2.2.1 _ hz' hs m
  let χ := n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 3
  let J := n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 4
  have hvcomp := hv.comp hchart hmap
  apply n07a_angularJet_memLp_mul J (χ.smooth.mul hvcomp) n
  intro j hj
  exact n07a_angularJet_memLp_mul χ hvcomp j
    (fun k _ => n07a_current_chart_angular_memLp h04 href hcur z hz hz' hs m hv hLp k)

end ContinuousFlexibility.Analysis
