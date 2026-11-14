module

public import ContinuousFlexibility.Analysis.N07aCanonicalSourceBounds
public import ContinuousFlexibility.Analysis.N07aCurrentPhysicalGeometry

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε γ : ℝ}

theorem n07a_canonicalAtomField_periodic
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (m : ℕ) (hm : K.left m < K.right m) (a : CanonicalGeometry.Atom)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) :
    ∀ y ∈ canonicalOpen S K m,
      n07aCanonicalAtomField D T S C L K a z m (y + (0, Real.pi)) =
        n07aCanonicalAtomField D T S C L K a z m y := by
  intro y hy
  have hx := n07aCanonicalUnitInversePoint_maps hm hy
  have hshift : n07aCanonicalUnitInversePoint K m (y + (0, Real.pi)) =
      n07aCanonicalUnitInversePoint K m y + (0, Real.pi) := by
    ext <;> simp only [n07aCanonicalUnitInversePoint, Prod.fst_add, Prod.snd_add,
      Prod.fst, Prod.snd, add_zero]
  change CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m a
    (n07aCanonicalUnitInversePoint K m (y + (0, Real.pi))) = _
  rw [hshift]
  exact (hcur.1 z hz m a).2 _ hx

theorem n07a_canonicalSource_contDiffOn
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (m : ℕ) :
    ContDiffOn ℝ ∞ (canonicalSource S K (liftSectorParameter S C z) m f)
      (canonicalOpen S K m) := by
  have hinterval := h04.1.referenceBounds m
  have hgeom := h04.1.charts _
    (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
    (hrefState.liftSectorParameter_sector z) m
  have hmaps : MapsTo (K.inverseChart (liftSectorParameter S C z) m)
      (canonicalOpen S K m) (annularOpen D) :=
    fun y hy => (h04.1.domains _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).2.2.1 (hgeom.2.1 hy)
  rw [n07a_canonicalSource_eq_sourceFactor (D := D) (T := T) (S := S) (C := C) (L := L)
    m hinterval.2.1 z f]
  exact (n07a_canonicalAtomField_smooth hcur (fun m => (h04.1.referenceBounds m).2.1)
    .sourceFactor z hz m).mul (hf.comp hgeom.2.2.2.2.2.1 hmaps)

theorem n07a_canonicalSource_periodic_on
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    {f : PolarPoint → ℝ} (hf : Function.Periodic f (0, Real.pi)) (m : ℕ) :
    ∀ y ∈ canonicalOpen S K m,
      canonicalSource S K (liftSectorParameter S C z) m f (y + (0, Real.pi)) =
        canonicalSource S K (liftSectorParameter S C z) m f y := by
  have hgeom := h04.1.charts _
    (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
    (hrefState.liftSectorParameter_sector z) m
  have hper := n07a_current_inverseChart_periodic h04
    (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
    (hrefState.liftSectorParameter_sector z) m
  intro y hy
  have hA := n07a_canonicalAtomField_periodic hcur m (h04.1.referenceBounds m).2.1
    .sourceFactor z hz y hy
  rw [n07a_canonicalSource_eq_sourceFactor (D := D) (T := T) (S := S) (C := C) (L := L)
    m (h04.1.referenceBounds m).2.1 z f]
  change _ * f (K.inverseChart (liftSectorParameter S C z) m (y + (0, Real.pi))) = _
  rw [hA, hper y hy, hf]

theorem n07a_canonicalSource_even_on
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hf : ∀ r θ, f (r, -θ) = f (r, θ)) (m : ℕ) :
    ∀ y ∈ canonicalOpen S K m,
      canonicalSource S K z m f (y.1, -y.2) = canonicalSource S K z m f y := by
  intro y hy
  have hx := (h04.1.charts z hz hs m).2.1 hy
  have hInv := h04.1.inverseReflection z hz hs m y hy
  have hreflect := h04.1.reflection z hz hs m _ hx
  simp only [canonicalSource, hInv, hreflect.2.1, hreflect.2.2, hf]

end ContinuousFlexibility.Analysis
