import ContinuousFlexibility.Analysis.N06CanonicalProperties
import ContinuousFlexibility.Analysis.N05ReferenceResidual
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Replacing current charts while retaining the original reference graph

The canonical intervals, physical reference endpoints, material labels and
reference coordinate germs determine the original N05 spaces and graph.
Replacing the current coordinate fields and their actual physical domains
preserves that same graph and inverse, including every weighted estimate.
Equality is needed only on the open reference pieces; arbitrary values of
inverse charts at endpoints are not used. The construction of the
replacement's N04 properties remains a separate obligation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Use the new current fields and actual domains, retaining the old
canonical intervals, physical reference endpoints and material labels. -/
def n06CurrentAtlasReplacement {S : PhysicalSpacesData}
    (K J : CanonicalData S) : CanonicalData S :=
  { K with
    physicalDomain := J.physicalDomain
    chart := J.chart
    inverseChart := J.inverseChart
    height := J.height
    coefficients := J.coefficients
    potential := J.potential
    dividedDifference := J.dividedDifference }

/-- The stored jets and the actual forget map are unchanged. -/
def n06RetainedVolumeModel {S : PhysicalSpacesData} {K : CanonicalData S}
    (J : CanonicalData S) (V : VolumeModelData S K) :
    VolumeModelData S (n06CurrentAtlasReplacement K J) where
  level := V.level
  forget := V.forget

/-- The same submodule, bounded inverse and all-level inverse are retained. -/
def n06RetainedCanonicalDomain {S : PhysicalSpacesData} {K : CanonicalData S}
    (J : CanonicalData S) {V : VolumeModelData S K} {b : ℕ}
    (B : CanonicalDomainData S K V b) :
    CanonicalDomainData S (n06CurrentAtlasReplacement K J)
      (n06RetainedVolumeModel J V) b where
  weakExponent := B.weakExponent
  sourceMaterial := B.sourceMaterial
  outputMaterial := B.outputMaterial
  lossMaterial := B.lossMaterial
  graph := B.graph
  inverse := B.inverse
  globalInverse := B.globalInverse

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K J : CanonicalData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n06_retainedVolumeModel_isVolumeModel {V : VolumeModelData S K}
    (hV : IsVolumeModel T S K V) :
    IsVolumeModel T S (n06CurrentAtlasReplacement K J)
      (n06RetainedVolumeModel J V) := hV

/-- On equal actual domains, the open inverses agree because the two forward
charts agree. No identification of endpoint values is required. -/
theorem n06_currentAtlasReplacement_inverse_eq
    (hK : N04PartA D S C K base ε)
    (hJ : N04PartA D S C (n06CurrentAtlasReplacement K J) base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hdomains : ∀ m, physicalPieceOpen S (n06CurrentAtlasReplacement K J) z m =
      physicalPieceOpen S K z m)
    (hchart : ∀ m, EqOn (J.chart z m) (K.chart z m) (physicalPieceOpen S K z m))
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    J.inverseChart z m p = K.inverseChart z m p := by
  obtain ⟨_, _, hleft, _, _, _, _, _⟩ := hK.charts z hz hs m
  obtain ⟨_, hmap, _, hright, _, _, _, _⟩ := hJ.charts z hz hs m
  have hq : J.inverseChart z m p ∈ physicalPieceOpen S K z m := by
    have hq' := hmap hp
    change J.inverseChart z m p ∈
      physicalPieceOpen S (n06CurrentAtlasReplacement K J) z m at hq'
    rw [hdomains m] at hq'
    exact hq'
  have he : K.chart z m (J.inverseChart z m p) = p :=
    (hchart m hq).symm.trans (hright p hp)
  have hi := hleft _ hq
  rw [he] at hi
  exact hi.symm

/-- Height and source transforms of arbitrary physical fields agree on the
actual open canonical cylinder. The source equality uses the forward
chart's derivative germ, not only its point value. -/
theorem n06_currentAtlasReplacement_transforms_eq
    (hK : N04PartA D S C K base ε)
    (hJ : N04PartA D S C (n06CurrentAtlasReplacement K J) base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hdomains : ∀ m, physicalPieceOpen S (n06CurrentAtlasReplacement K J) z m =
      physicalPieceOpen S K z m)
    (hchart : ∀ m, EqOn (J.chart z m) (K.chart z m) (physicalPieceOpen S K z m))
    (hheight : ∀ m, EqOn (J.height z m) (K.height z m) (physicalPieceOpen S K z m))
    (m : ℕ) (f : PolarPoint → ℝ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S (n06CurrentAtlasReplacement K J) z m f p =
        canonicalHeight S K z m f p ∧
      canonicalSource S (n06CurrentAtlasReplacement K J) z m f p =
        canonicalSource S K z m f p := by
  have hG := n06_currentAtlasReplacement_inverse_eq hK hJ hz hs hdomains hchart m hp
  have hq : K.inverseChart z m p ∈ physicalPieceOpen S K z m :=
    (hK.charts z hz hs m).2.1 hp
  have hnear : J.chart z m =ᶠ[𝓝 (K.inverseChart z m p)] K.chart z m := by
    filter_upwards [(hK.domains z hz hs m).1.mem_nhds hq] with x hx
    exact hchart m hx
  have hd : fderiv ℝ (J.chart z m) (K.inverseChart z m p) =
      fderiv ℝ (K.chart z m) (K.inverseChart z m p) := hnear.fderiv_eq
  have hJac : planeJacobian (J.chart z m) (K.inverseChart z m p) =
      planeJacobian (K.chart z m) (K.inverseChart z m p) := by
    simp only [planeJacobian, hd]
  constructor
  · change f (J.inverseChart z m p) / J.height z m (J.inverseChart z m p) = _
    rw [hG, hheight m hq]
    rfl
  · change J.height z m (J.inverseChart z m p) * f (J.inverseChart z m p) /
        |planeJacobian (J.chart z m) (J.inverseChart z m p)| = _
    rw [hG, hheight m hq, hJac]
    rfl

theorem n06_currentAtlasReplacement_representation_iff
    (hK : N04PartA D S C K base ε)
    (hJ : N04PartA D S C (n06CurrentAtlasReplacement K J) base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hdomains : ∀ m, physicalPieceOpen S (n06CurrentAtlasReplacement K J) z m =
      physicalPieceOpen S K z m)
    (hchart : ∀ m, EqOn (J.chart z m) (K.chart z m) (physicalPieceOpen S K z m))
    (hheight : ∀ m, EqOn (J.height z m) (K.height z m) (physicalPieceOpen S K z m))
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K) (η f : PolarPoint → ℝ) :
    HasCanonicalRepresentation D S C (n06CurrentAtlasReplacement K J) z U F η f ↔
      HasCanonicalRepresentation D S C K z U F η f := by
  have ht (m : ℕ) (g : PolarPoint → ℝ) :
      canonicalHeight S (n06CurrentAtlasReplacement K J) z m g
          =ᵐ[canonicalMeasure S K m] canonicalHeight S K z m g ∧
        canonicalSource S (n06CurrentAtlasReplacement K J) z m g
          =ᵐ[canonicalMeasure S K m] canonicalSource S K z m g := by
    have hpair : ∀ᵐ p ∂canonicalMeasure S K m,
        canonicalHeight S (n06CurrentAtlasReplacement K J) z m g p =
            canonicalHeight S K z m g p ∧
          canonicalSource S (n06CurrentAtlasReplacement K J) z m g p =
            canonicalSource S K z m g p := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
      exact n06_currentAtlasReplacement_transforms_eq hK hJ hz hs hdomains hchart hheight
        m g ⟨hp.1, mem_univ _⟩
    exact ⟨hpair.mono (fun _ hp => hp.1), hpair.mono (fun _ hp => hp.2)⟩
  constructor
  · rintro ⟨hU, hF⟩
    exact ⟨fun m => (hU m).trans (ht m _).1, fun m => (hF m).trans (ht m f).2⟩
  · rintro ⟨hU, hF⟩
    exact ⟨fun m => (hU m).trans (ht m _).1.symm,
      fun m => (hF m).trans (ht m f).2.symm⟩

/-- The literal reference relation, including physical normalization and
the three original scalar columns, is unchanged. -/
theorem n06_currentAtlasReplacement_referenceRelation_iff {V : VolumeModelData S K}
    (hK : N04PartA D S C K base ε)
    (hJ : N04PartA D S C (n06CurrentAtlasReplacement K J) base ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState)
    (hchart : ∀ m, EqOn (J.chart (C.referenceState, 0) m)
      (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    (hheight : ∀ m, EqOn (J.height (C.referenceState, 0) m)
      (K.height (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    (γ M₀ M₁ ell : ℝ) (U : CanonicalUnknown S K) (F : CanonicalSequence S K) :
    ReferenceCanonicalRelation D T S C (n06CurrentAtlasReplacement K J)
        (n06RetainedVolumeModel J V) γ M₀ M₁ ell U F ↔
      ReferenceCanonicalRelation D T S C K V γ M₀ M₁ ell U F := by
  have hdomains : ∀ m,
      physicalPieceOpen S (n06CurrentAtlasReplacement K J) (C.referenceState, 0) m =
        physicalPieceOpen S K (C.referenceState, 0) m := by
    intro m
    calc
      _ = referencePhysicalPieceOpen S (n06CurrentAtlasReplacement K J) m :=
        hJ.referenceDomain m
      _ = referencePhysicalPieceOpen S K m := rfl
      _ = _ := (hK.referenceDomain m).symm
  have hchart' : ∀ m, EqOn (J.chart (C.referenceState, 0) m)
      (K.chart (C.referenceState, 0) m) (physicalPieceOpen S K (C.referenceState, 0) m) := by
    intro m p hp
    exact hchart m (by simpa only [hK.referenceDomain m] using hp)
  have hheight' : ∀ m, EqOn (J.height (C.referenceState, 0) m)
      (K.height (C.referenceState, 0) m) (physicalPieceOpen S K (C.referenceState, 0) m) := by
    intro m p hp
    exact hheight m (by simpa only [hK.referenceDomain m] using hp)
  constructor
  · rintro ⟨hU, η, f, hrep, hgraph⟩
    exact ⟨hU, η, f, (n06_currentAtlasReplacement_representation_iff hK hJ hz hs
      hdomains hchart' hheight' U F η f).mp hrep, hgraph⟩
  · rintro ⟨hU, η, f, hrep, hgraph⟩
    exact ⟨hU, η, f, (n06_currentAtlasReplacement_representation_iff hK hJ hz hs
      hdomains hchart' hheight' U F η f).mpr hrep, hgraph⟩

/-- All N05 clauses retain the same source level, graph and inverse. In
particular, this transports the all-exponent estimates and the weak first
normal derivative without deriving new bounds for an unrelated inverse. -/
theorem n06_currentAtlasReplacement_N05
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hK : N04PartA D S C K base ε)
    (hJ : N04PartA D S C (n06CurrentAtlasReplacement K J) base ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState)
    (hchart : ∀ m, EqOn (J.chart (C.referenceState, 0) m)
      (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    (hheight : ∀ m, EqOn (J.height (C.referenceState, 0) m)
      (K.height (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    (h05 : N05Properties D T S C K V b B) :
    N05Properties D T S C (n06CurrentAtlasReplacement K J)
      (n06RetainedVolumeModel J V) b (n06RetainedCanonicalDomain J B) := by
  obtain ⟨hb, hV, hγ, hγlt, hell, hclosed, hgraph, hright, hleft, hglobal,
    hbase, hthree, hall, hnormal⟩ := h05
  refine ⟨hb, n06_retainedVolumeModel_isVolumeModel hV, hγ, hγlt, hell, hclosed,
    ?_, hright, hleft, hglobal, hbase, hthree, hall, hnormal⟩
  intro u
  exact (hgraph u).trans
    (n06_currentAtlasReplacement_referenceRelation_iff hK hJ hz hs hchart hheight
      B.weakExponent B.sourceMaterial B.outputMaterial B.lossMaterial u.1
        (V.forget (3 / 4 : ℝ) 0 b u.2)).symm

/-- A current-coordinate construction retaining the reference germs can
keep the complete original Through05 witness. -/
theorem n06_currentAtlasReplacement_through05
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {V : VolumeModelData S K} {b loss : ℕ} {B : CanonicalDomainData S K V b}
    (h05 : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (h04 : NonlinearPropertiesThrough04 D T S C R L
      (n06CurrentAtlasReplacement K J) base loss ε)
    (hchart : ∀ m, EqOn (J.chart (C.referenceState, 0) m)
      (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m))
    (hheight : ∀ m, EqOn (J.height (C.referenceState, 0) m)
      (K.height (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m)) :
    NonlinearPropertiesThrough05 D T S C R L (n06CurrentAtlasReplacement K J)
      (n06RetainedVolumeModel J V) b (n06RetainedCanonicalDomain J B) base loss ε := by
  have h01 : N01Properties D T S C base loss ε := h05.1.1.1.1
  have hK := (n06_N04_qualitative_parts h05.1.2.2.2.2).1
  have hJ := (n06_N04_qualitative_parts h04.2.2.2.2).1
  exact ⟨h04, n06_currentAtlasReplacement_N05 hK hJ
    (n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1)
    (n05_referenceState_sector h01.2.2.1) hchart hheight h05.2⟩

end ContinuousFlexibility.Statements
