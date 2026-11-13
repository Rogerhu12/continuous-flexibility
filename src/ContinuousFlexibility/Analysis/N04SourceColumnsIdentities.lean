import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
import ContinuousFlexibility.Analysis.N07aAngularJacobianEnvelope
import ContinuousFlexibility.Scalar.WeightedPartialIdentities

/-!
# Source atoms in the same inverse-chart coordinates

The geometry Jacobian atoms are evaluated on the fixed physical strip.  The
source factor instead evaluates the Jacobian at the actual inverse-chart
point.  The inverse determinant identity below expresses that factor using
the first spatial derivatives of the two inverse-coordinate atoms, on the
canonical unit strip itself.  It therefore also applies to moving negative
pieces, whose inverse points need not lie in the reference physical strip.

The scalar columns are exact products of this source factor and the physical
fields already pulled back in the subnode interface.  Every identity applies
to the current and reference state of the same atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

/-- The canonical source is a scalar multiplier times the actual pulled
physical forcing. This identity does not need a nonvanishing hypothesis. -/
theorem n04SourceColumns_source_eq_product
    (z : AnnularState S × ℝ) (m : ℕ) (f : PolarPoint → ℝ) (p : PolarPoint) :
    canonicalSource S K z m f (canonicalUnitPoint K m p) =
      atom D T S C L K z m .sourceFactor p *
        f (K.inverseChart z m (canonicalUnitPoint K m p)) := by
  simp only [atom, canonicalSource, mul_one, div_eq_mul_inv]
  ring

/-- No parameter is changed when converting the left column to a product. -/
theorem n04SourceColumns_left_eq_product
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) :
    atom D T S C L K z m .leftColumn p =
      atom D T S C L K z m .sourceFactor p *
        divergenceOperator (L.coefficients z) (fun q => S.chiLeft q.1)
          (K.inverseChart z m (canonicalUnitPoint K m p)) :=
  n04SourceColumns_source_eq_product z m _ p

/-- The same product formula gives the physical `ν` column. -/
theorem n04SourceColumns_nu_eq_product
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) :
    atom D T S C L K z m .nuColumn p =
      atom D T S C L K z m .sourceFactor p *
        nuColumnField D S C z (K.inverseChart z m (canonicalUnitPoint K m p)) :=
  n04SourceColumns_source_eq_product z m _ p

/-- The normalized inverse-coordinate atoms recover the original inverse
chart at every canonical unit point, including outside the open strip. -/
theorem n04SourceColumns_inverseChart_unit_eq
    (z : AnnularState S × ℝ) (m : ℕ)
    (hwidth : K.physicalRight m - K.physicalLeft m ≠ 0) :
    (fun p => K.inverseChart z m (canonicalUnitPoint K m p)) =
      (fun p =>
        (K.physicalLeft m + (K.physicalRight m - K.physicalLeft m) *
          atom D T S C L K z m .inverseRadial p,
        p.2 + atom D T S C L K z m .inverseAngleDefect p)) := by
  funext p
  apply Prod.ext
  · change (K.inverseChart z m (canonicalUnitPoint K m p)).1 =
      K.physicalLeft m + (K.physicalRight m - K.physicalLeft m) *
        (((K.inverseChart z m (canonicalUnitPoint K m p)).1 - K.physicalLeft m) /
          (K.physicalRight m - K.physicalLeft m))
    field_simp [hwidth]
    <;> ring
  · change (K.inverseChart z m (canonicalUnitPoint K m p)).2 =
      p.2 + ((K.inverseChart z m (canonicalUnitPoint K m p)).2 - p.2)
    ring

/-- The determinant of a normalized radial component and angle defect is
an explicit polynomial in their genuine first derivatives. -/
theorem n04SourceColumns_planeJacobian_coordinatePair
    {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (d c : ℝ) :
    planeJacobian (fun q => (d + c * f q, q.2 + g q)) p =
      c * (radialPartial f p * (1 + angularPartial g p) -
        radialPartial g p * angularPartial f p) := by
  have hr : HasFDerivAt (fun q => d + c * f q) (c • fderiv ℝ f p) p :=
    (hf.hasFDerivAt.const_mul c).const_add d
  have ha : HasFDerivAt (fun q : PolarPoint => q.2 + g q)
      (ContinuousLinearMap.snd ℝ ℝ ℝ + fderiv ℝ g p) p :=
    hasFDerivAt_snd.add hg.hasFDerivAt
  simp only [planeJacobian, (hr.prodMk ha).fderiv, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, radialPartial, angularPartial]
  ring

/-- The affine canonical unit map contributes exactly its stored width. -/
theorem n04SourceColumns_planeJacobian_unitPoint (m : ℕ) (p : PolarPoint) :
    planeJacobian (canonicalUnitPoint K m) p = K.right m - K.left m := by
  have hr : HasFDerivAt
      (fun q : PolarPoint => K.left m + (K.right m - K.left m) * q.1)
      ((K.right m - K.left m) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (hasFDerivAt_fst.const_mul (K.right m - K.left m)).const_add (K.left m)
  have ha : HasFDerivAt (fun q : PolarPoint => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  change planeJacobian (fun q : PolarPoint =>
    (K.left m + (K.right m - K.left m) * q.1, q.2)) p = _
  simp only [planeJacobian, (hr.prodMk ha).fderiv, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- The inverse Jacobian at the actual canonical point is obtained from
the two normalized inverse atoms, without evaluation on a physical strip. -/
theorem n04SourceColumns_inverseJacobian_unit
    (z : AnnularState S × ℝ) (m : ℕ)
    (hphysical : K.physicalRight m - K.physicalLeft m ≠ 0)
    (hcanonical : K.right m - K.left m ≠ 0) (p : PolarPoint)
    (hinverse : DifferentiableAt ℝ (K.inverseChart z m) (canonicalUnitPoint K m p))
    (hradial : DifferentiableAt ℝ (atom D T S C L K z m .inverseRadial) p)
    (hangle : DifferentiableAt ℝ (atom D T S C L K z m .inverseAngleDefect) p) :
    planeJacobian (K.inverseChart z m) (canonicalUnitPoint K m p) =
      ((K.physicalRight m - K.physicalLeft m) / (K.right m - K.left m)) *
        (radialPartial (atom D T S C L K z m .inverseRadial) p *
            (1 + angularPartial (atom D T S C L K z m .inverseAngleDefect) p) -
          radialPartial (atom D T S C L K z m .inverseAngleDefect) p *
            angularPartial (atom D T S C L K z m .inverseRadial) p) := by
  have hu : DifferentiableAt ℝ (canonicalUnitPoint K m) p :=
    (differentiableAt_const.add (differentiableAt_const.mul differentiableAt_fst)).prodMk
      differentiableAt_snd
  have hcomp := planeJacobian_comp hu hinverse
  have hpair := n04SourceColumns_planeJacobian_coordinatePair hradial hangle
    (K.physicalLeft m) (K.physicalRight m - K.physicalLeft m)
  have heq := n04SourceColumns_inverseChart_unit_eq (D := D) (T := T) (C := C)
    (L := L) z m hphysical
  have hscaled :
      planeJacobian (K.inverseChart z m) (canonicalUnitPoint K m p) *
          (K.right m - K.left m) =
        (K.physicalRight m - K.physicalLeft m) *
          (radialPartial (atom D T S C L K z m .inverseRadial) p *
              (1 + angularPartial (atom D T S C L K z m .inverseAngleDefect) p) -
            radialPartial (atom D T S C L K z m .inverseAngleDefect) p *
              angularPartial (atom D T S C L K z m .inverseRadial) p) := by
    rw [n04SourceColumns_planeJacobian_unitPoint] at hcomp
    exact hcomp.symm.trans ((congrArg (fun F => planeJacobian F p) heq).trans hpair)
  calc
    _ = ((K.physicalRight m - K.physicalLeft m) *
        (radialPartial (atom D T S C L K z m .inverseRadial) p *
            (1 + angularPartial (atom D T S C L K z m .inverseAngleDefect) p) -
          radialPartial (atom D T S C L K z m .inverseAngleDefect) p *
            angularPartial (atom D T S C L K z m .inverseRadial) p)) /
        (K.right m - K.left m) := (eq_div_iff hcanonical).mpr hscaled
    _ = _ := by ring

/-- A genuine chart inverse gives the source factor as the product of
the pulled height and the absolute inverse-chart determinant. -/
theorem n04SourceColumns_sourceFactor_eq_inverseJacobian
    {base : ℕ} {ε : ℝ} (hgeom : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : canonicalUnitPoint K m p ∈ canonicalOpen S K m) :
    atom D T S C L K z m .sourceFactor p =
      K.height z m (K.inverseChart z m (canonicalUnitPoint K m p)) *
        |planeJacobian (K.inverseChart z m) (canonicalUnitPoint K m p)| := by
  rw [n07a_actual_inverseChart_jacobian_abs hgeom hz hs m hp]
  simp only [atom, canonicalSource, mul_one, div_eq_mul_inv]

/-- The same inverse determinant formula, written solely with first mixed
jets of the normalized inverse-coordinate atoms. -/
theorem n04SourceColumns_sourceFactor_eq_mixedDeterminant
    {base : ℕ} {ε : ℝ} (hgeom : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hradial : ContDiffOn ℝ ∞ (atom D T S C L K z m .inverseRadial) unitStrip)
    (hangle : ContDiffOn ℝ ∞ (atom D T S C L K z m .inverseAngleDefect) unitStrip)
    {p : PolarPoint} (hp : p ∈ unitStrip)
    (hq : canonicalUnitPoint K m p ∈ canonicalOpen S K m) :
    atom D T S C L K z m .sourceFactor p =
      K.height z m (K.inverseChart z m (canonicalUnitPoint K m p)) *
        |((K.physicalRight m - K.physicalLeft m) / (K.right m - K.left m)) *
          (mixedDerivative 1 0 (atom D T S C L K z m .inverseRadial) p *
              (1 + mixedDerivative 0 1 (atom D T S C L K z m .inverseAngleDefect) p) -
            mixedDerivative 1 0 (atom D T S C L K z m .inverseAngleDefect) p *
              mixedDerivative 0 1 (atom D T S C L K z m .inverseRadial) p)| := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hi : DifferentiableAt ℝ (K.inverseChart z m) (canonicalUnitPoint K m p) :=
    ((hgeom.charts z hz hs m).2.2.2.2.2.1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  have hr := (hradial.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have ha := (hangle.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [n04SourceColumns_sourceFactor_eq_inverseJacobian hgeom hz hs m hq,
    n04SourceColumns_inverseJacobian_unit z m
      (sub_pos.mpr (hgeom.referenceBounds m).1).ne'
      (sub_pos.mpr (hgeom.referenceBounds m).2.1).ne' p hi hr ha]
  rw [radialPartial_eq_mixedDerivative_on hU hradial hp,
    angularPartial_eq_mixedDerivative_on hU hangle hp,
    radialPartial_eq_mixedDerivative_on hU hangle hp,
    angularPartial_eq_mixedDerivative_on hU hradial hp]

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- Exact current product on the very atlas in the obligation. -/
theorem sourceColumns_leftFamily_eq :
    G.atomFamily η .leftColumn = fun z m p =>
      G.atomFamily η .sourceFactor z m p * G.pulled η (G.leftColumnField η) z m p := by
  funext z m p
  exact n04SourceColumns_left_eq_product (G.lift η z) m p

/-- Reference and current products use the identical stored fields. -/
theorem sourceColumns_leftRef_eq :
    G.atomRef η .leftColumn = fun m p =>
      G.atomRef η .sourceFactor m p * G.pulledRef η (G.leftColumnField η) m p := by
  funext m p
  exact n04SourceColumns_left_eq_product (G.ref η) m p

theorem sourceColumns_nuFamily_eq :
    G.atomFamily η .nuColumn = fun z m p =>
      G.atomFamily η .sourceFactor z m p * G.pulled η (G.nuField η) z m p := by
  funext z m p
  exact n04SourceColumns_nu_eq_product (G.lift η z) m p

theorem sourceColumns_nuRef_eq :
    G.atomRef η .nuColumn = fun m p =>
      G.atomRef η .sourceFactor m p * G.pulledRef η (G.nuField η) m p := by
  funext m p
  exact n04SourceColumns_nu_eq_product (G.ref η) m p

theorem sourceColumns_inverseFamily_eq :
    G.atomFamily η .sourceFactorInverse = fun z m p =>
      (G.atomFamily η .sourceFactor z m p)⁻¹ := rfl

theorem sourceColumns_inverseRef_eq :
    G.atomRef η .sourceFactorInverse = fun m p =>
      (G.atomRef η .sourceFactor m p)⁻¹ := rfl

/-- The raw denominator is evaluated at `pulledPoint`, rather than at
the fixed physical unit point used by the Jacobian atom. -/
theorem sourceColumns_factorFamily_eq :
    G.atomFamily η .sourceFactor = fun z m p =>
      G.pulledHeight η z m p /
        |planeJacobian ((G.V η).chart (G.lift η z) m)
          (G.pulledPoint η (G.lift η z) m p)| := by
  funext z m p
  simp only [atomFamily, atom, canonicalSource, mul_one, pulledHeight, heightField,
    pulledPoint]

theorem sourceColumns_factorRef_eq :
    G.atomRef η .sourceFactor = fun m p =>
      G.pulledHeightRef η m p /
        |planeJacobian ((G.V η).chart (G.ref η) m)
          (G.pulledPoint η (G.ref η) m p)| := by
  funext m p
  simp only [atomRef, atom, canonicalSource, mul_one, pulledHeightRef, heightField,
    pulledPoint]

end N04RealizationGauge

end ContinuousFlexibility.Analysis
