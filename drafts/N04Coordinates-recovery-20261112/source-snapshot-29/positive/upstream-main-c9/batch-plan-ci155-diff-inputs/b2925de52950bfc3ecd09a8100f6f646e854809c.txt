import ContinuousFlexibility.Analysis.N06PrimitiveReferenceTransport
import ContinuousFlexibility.Analysis.N06ReferenceProjectionRemainder

/-!
# Original L2 cutoffs under the primitive radial reference geometry

The canonical Fourier cutoffs are identified with the actual physical
projections without a material-label or coordinate-cost assumption.
AE identities in the original physical measure pass through both genuine
transforms, and the original left scalar is retained exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open CanonicalGeometry ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The actual height cutoff is the physical projection in reference coordinates. -/
theorem n06_primitiveReferenceHeight_fourierCut_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
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
    have hcircle := n06_primitiveReferenceHeight_circle h hradial η m hpr
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
  exact (n06_primitiveReferenceHeight_projection h hradial
    (Finset.range (N + 1)) η m ⟨hp.1, mem_univ _⟩).symm

/-- The original source L2 cutoff is the actual source transformation
of the physical projection. The true Jacobian and height are kept. -/
theorem n06_primitiveReferenceSource_fourierCut_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
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
      exact n06_primitiveReferenceSource_circle h hradial f m
        (p := (r, 0)) ⟨hr, mem_univ _⟩ η
    change canonicalSource S K (C.referenceState, 0) m f (r, θ + Real.pi) =
      canonicalSource S K (C.referenceState, 0) m f (r, θ)
    rw [hcircle (θ + Real.pi), hcircle θ]
    apply congrArg (fun a : ℝ => A * a)
    simpa only [Prod.mk_add_mk, add_zero] using hfp (x.1, θ)
  apply (n06CanonicalFourierCutL2_coe_referenceProjection_ae F he hrep hp N).trans
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact (n06_primitiveReferenceSource_projection h hradial
    (Finset.range (N + 1)) f m ⟨hp.1, mem_univ _⟩).symm


/-- Both actual transformations respect the original physical AE class.
The chart is used only on its genuine reference domain. -/
theorem n06_primitiveReferenceTransforms_congr_ae_physical
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[radialPhysicalMeasure D] g) (m : ℕ) :
    canonicalHeight S K (C.referenceState, 0) m f
      =ᵐ[canonicalMeasure S K m] canonicalHeight S K (C.referenceState, 0) m g ∧
    canonicalSource S K (C.referenceState, 0) m f
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m g := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hc := h04.1.charts (C.referenceState, 0) href hs m
  have hhalf : f =ᵐ[volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)] g := by
    apply ae_restrict_of_ae_restrict_of_subset _ hfg
    intro p hp
    exact ⟨(h04.1.referenceBounds m).2.2 hp.1, hp.2.1,
      hp.2.2.trans (by linarith [Real.pi_pos])⟩
  have hangle : ∀ p ∈ physicalPieceOpen S K (C.referenceState, 0) m,
      (K.chart (C.referenceState, 0) m p).2 = p.2 := by
    intro p hp
    have hp' : p ∈ referencePhysicalPieceOpen S K m := by
      simpa only [h04.1.referenceDomain m] using hp
    simpa only using congrArg Prod.snd (hradial.1 m p hp').1
  have hpull : ∀ᵐ p ∂canonicalMeasure S K m,
      f (K.inverseChart (C.referenceState, 0) m p) =
        g (K.inverseChart (C.referenceState, 0) m p) := by
    apply (n05_canonicalChart_ae_iff h04 href hs m hangle _).mpr
    simp only [n05PhysicalPieceHalfPeriod, h04.1.referenceDomain m, referencePhysicalPieceOpen,
      prod_inter_prod, inter_univ, univ_inter]
    filter_upwards [hhalf,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpU
    have hpo : p ∈ physicalPieceOpen S K (C.referenceState, 0) m := by
      rw [h04.1.referenceDomain m]
      exact ⟨hpU.1, mem_univ _⟩
    simpa only [hc.2.2.1 p hpo] using hp
  constructor
  · filter_upwards [hpull] with p hp
    simp only [canonicalHeight, hp]
  · filter_upwards [hpull] with p hp
    simp only [canonicalSource, hp]

/-- The source's actual left scalar remains unchanged under projection. -/
theorem n06_primitiveReferenceRemainder_fourierCut_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K)
    (m : ℕ) (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ))
    {η : PolarPoint → ℝ} (hη : MemLp η 2 (radialPhysicalMeasure D))
    (hηp : Function.Periodic η (0, Real.pi)) (aL : ℝ)
    (hrep : (U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m
        (fun p => η p - aL * S.chiLeft p.1)) (N : ℕ) :
    (n06CanonicalFourierCutL2 N U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m
        (fun p => referenceBasisProjection (Finset.range (N + 1)) η p -
          aL * S.chiLeft p.1) := by
  have hperiod : Function.Periodic (fun p : PolarPoint => η p - aL * S.chiLeft p.1)
      (0, Real.pi) := by
    intro p
    simp only [hηp p, Prod.fst_add, add_zero]
  have hcut := n06_primitiveReferenceHeight_fourierCut_ae
    h hradial m U he hperiod hrep N
  have hphysical := n06_referenceBasisProjection_sub_radial_ae hη
    (fun r => aL * S.chiLeft r)
    (I := Finset.range (N + 1)) (Finset.mem_range.mpr (Nat.zero_lt_succ N))
  exact hcut.trans (n06_primitiveReferenceTransforms_congr_ae_physical h hradial hphysical m).1


end ContinuousFlexibility.Statements
