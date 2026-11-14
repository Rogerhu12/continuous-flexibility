module

public import ContinuousFlexibility.Analysis.N06PhysicalRepresentativeUniqueness
public import ContinuousFlexibility.Analysis.N06PhysicalNormalization
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Periodic reconstruction with the original physical normalization

The reference row depends only on the physical representative almost
everywhere on the annulus. Canonical equality therefore transfers the row
from the actual N05 graph representative to the explicit periodic
reconstruction. N04 fixes that reconstruction on the normalization region,
so the same conclusion holds at every admissible current state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem n06_referenceRow_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {η ξ : PolarPoint → ℝ}
    (heq : η =ᵐ[volume.restrict (annularOpen D)] ξ) :
    referenceRow D η = referenceRow D ξ := by
  have hmeasure : (volume.restrict (Ioo D.a D.b)).prod (volume : Measure ℝ) =
      volume.restrict (annularOpen D) := by
    change _ = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Ioo D.a D.b ×ˢ univ)
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hprod : η =ᵐ[(volume.restrict (Ioo D.a D.b)).prod (volume : Measure ℝ)] ξ := by
    rwa [hmeasure]
  have hfib := Measure.ae_ae_of_ae_prod hprod
  have hrow : (fun r => referenceColumn D r * referenceMode η 2 r) =ᵐ[
      volume.restrict (Ioo D.a D.b)]
      (fun r => referenceColumn D r * referenceMode ξ 2 r) := by
    filter_upwards [hfib] with r hr
    apply congrArg (fun x : ℝ => referenceColumn D r * x)
    unfold referenceMode radialAngularMean
    apply congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x)
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hr] with θ hθ
    intro _
    rw [hθ]
  have hrestrict : (volume : Measure ℝ).restrict (Ioo D.a D.b) =
      volume.restrict (Ioc D.a D.b) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [hrestrict] at hrow
  unfold referenceRow
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_congr_ae hrow

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The explicit reconstruction agrees almost everywhere with any periodic
physical representative of the same canonical unknown. -/
theorem n06PhysicalHeight_ae_eq
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {U : CanonicalUnknown S K}
    {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (hη : Function.Periodic η (0, Real.pi)) :
    n06PhysicalHeight K z (fun m => (U.1 m : PolarPoint → ℝ)) U.2.1 =ᵐ[
      volume.restrict (annularOpen D)] η := by
  have hnamed := n06_physical_representation hN04 hz hs U F
  have htail : Function.Periodic (fun p : PolarPoint => U.2.1 * S.chiLeft p.1)
      (0, Real.pi) := by
    intro p
    simp only [Prod.fst_add, add_zero]
  have hrem := n06_canonicalHeight_ae_injective hN04 hz hs
    (hnamed.2.sub htail) (hη.sub htail)
    (fun m => (hnamed.1.1 m).symm.trans (hrep.1 m))
  filter_upwards [hrem] with p hp
  exact sub_left_inj.mp hp

/-- The same named periodic height has the original normalization row. -/
theorem n06PhysicalHeight_normalized
    (hab : D.a ≤ D.b) (hN04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {Fref : CanonicalSequence S K}
    {ηref fref : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (C.referenceState, 0) U Fref ηref fref)
    (hperiod : Function.Periodic ηref (0, Real.pi)) (hrow : referenceRow D ηref = 0) :
    referenceRow D (n06PhysicalHeight K z (fun m => (U.1 m : PolarPoint → ℝ)) U.2.1) =
      0 := by
  rw [n06PhysicalHeight_referenceRow hN04 hz hs]
  exact (n06_referenceRow_congr_ae hab
    (n06PhysicalHeight_ae_eq hN04 href hsector hrep hperiod)).trans hrow

/-- Every member of the actual N05 graph has the explicit periodic current
representation and the same physical normalization. The weak current
equation is not assumed or inferred in this representation lemma. -/
theorem n06_graph_periodic_normalized_representation
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hab : D.a ≤ D.b) (hN04 : N04Properties D T S C L K base loss ε)
    (hN05 : N05Properties D T S C K V b B)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (u : B.Space) (F : CanonicalSequence S K) :
    HasCanonicalRepresentation D S C K z u.val.1 F
      (n06PhysicalHeight K z (fun m => (u.val.1.1 m : PolarPoint → ℝ)) u.val.1.2.1)
      (n06PhysicalSource K z (fun m => (F m : PolarPoint → ℝ))) ∧
    Function.Periodic
      (n06PhysicalHeight K z (fun m => (u.val.1.1 m : PolarPoint → ℝ)) u.val.1.2.1)
      (0, Real.pi) ∧
    referenceRow D
      (n06PhysicalHeight K z (fun m => (u.val.1.1 m : PolarPoint → ℝ)) u.val.1.2.1) = 0 := by
  have hgraph := hN05.2.2.2.2.2.2.1
  obtain ⟨_, ηref, fref, hrep, hweak⟩ := (hgraph u.val).mp u.property
  obtain ⟨aL, haL⟩ := hweak.1
  exact ⟨(n06_physical_representation hN04 hz hs u.val.1 F).1,
    (n06_physical_representation hN04 hz hs u.val.1 F).2,
    n06PhysicalHeight_normalized hab hN04 href hsector hz hs hrep haL.2.2.1
      hweak.2.2.1⟩

end ContinuousFlexibility.Statements
