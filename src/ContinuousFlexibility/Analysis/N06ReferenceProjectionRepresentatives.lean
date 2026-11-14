module

public import ContinuousFlexibility.Analysis.N06ReferenceProjectionTransport
public import ContinuousFlexibility.Analysis.N06CanonicalProperties

/-!
# Original L2 cutoffs represent actual physical reference projections

The physical and canonical projections are identified on the original
piece measures. The physical representative is only assumed periodic;
its local L2 information comes from the given canonical representation.
All scalar columns can therefore be retained separately, including an
arbitrary original compatibility field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The same canonical height L2 cutoff is the genuine transform of the
physical finite projection. No radial regularity or finite angular
spectrum of the original physical height is required. -/
theorem n06_controlledReferenceHeight_fourierCut_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ))
    {η : PolarPoint → ℝ} (hηp : Function.Periodic η (0, Real.pi))
    (hrep : (U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m η) (N : ℕ) :
    (n06CanonicalFourierCutL2 N U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m
        (referenceBasisProjection (Finset.range (N + 1)) η) := by
  have hp : ∀ r ∈ Ioo (K.left m) (K.right m),
      Function.Periodic
        (fun θ => canonicalHeight S K (C.referenceState, 0) m η (r, θ)) Real.pi := by
    intro r hr θ
    have hpr : (r, (0 : ℝ)) ∈ canonicalOpen S K m := ⟨hr, mem_univ _⟩
    have hcircle := n06_controlledReferenceHeight_circle h hcoordinates η m hpr
    change canonicalHeight S K (C.referenceState, 0) m η (r, θ + Real.pi) =
      canonicalHeight S K (C.referenceState, 0) m η (r, θ)
    rw [hcircle (θ + Real.pi), hcircle θ]
    apply congrArg (fun a : ℝ =>
      (K.height (C.referenceState, 0) m
        ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, 0))⁻¹ * a)
    simpa only [Prod.mk_add_mk, add_zero] using
      hηp ((K.inverseChart (C.referenceState, 0) m (r, 0)).1, θ)
  apply (n06CanonicalFourierCutL2_coe_referenceProjection_ae U he hrep hp N).trans
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact (n06_controlledReferenceHeight_projection h hcoordinates
    (Finset.range (N + 1)) η m ⟨hp.1, mem_univ _⟩).symm

/-- The original source L2 cutoff is the actual source transformation
of the physical projection. The true Jacobian and height are kept. -/
theorem n06_controlledReferenceSource_fourierCut_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) (F : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => F (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (F : PolarPoint → ℝ))
    {f : PolarPoint → ℝ} (hfp : Function.Periodic f (0, Real.pi))
    (hrep : (F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m f) (N : ℕ) :
    (n06CanonicalFourierCutL2 N F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m
        (referenceBasisProjection (Finset.range (N + 1)) f) := by
  have hp : ∀ r ∈ Ioo (K.left m) (K.right m),
      Function.Periodic
        (fun θ => canonicalSource S K (C.referenceState, 0) m f (r, θ)) Real.pi := by
    intro r hr θ
    let x := K.inverseChart (C.referenceState, 0) m (r, 0)
    let A : ℝ := K.height (C.referenceState, 0) m (x.1, 0) /
      |deriv (fun s => (K.chart (C.referenceState, 0) m (s, 0)).1) x.1|
    have hcircle (η : ℝ) :
        canonicalSource S K (C.referenceState, 0) m f (r, η) = A * f (x.1, η) := by
      have hj := n06_controlledReferenceSource_angularJet h hcoordinates f m 0
        (p := (r, η)) ⟨hr, mem_univ _⟩
      simp only [spaces_mixedDerivative_zero] at hj
      rw [n06_controlledReference_inverse_circle h hcoordinates m
        (p := (r, 0)) ⟨hr, mem_univ _⟩ η] at hj
      exact hj
    change canonicalSource S K (C.referenceState, 0) m f (r, θ + Real.pi) =
      canonicalSource S K (C.referenceState, 0) m f (r, θ)
    rw [hcircle (θ + Real.pi), hcircle θ]
    apply congrArg (fun a : ℝ => A * a)
    simpa only [Prod.mk_add_mk, add_zero] using hfp (x.1, θ)
  apply (n06CanonicalFourierCutL2_coe_referenceProjection_ae F he hrep hp N).trans
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact (n06_controlledReferenceSource_projection h hcoordinates
    (Finset.range (N + 1)) f m ⟨hp.1, mem_univ _⟩).symm

end ContinuousFlexibility.Statements
