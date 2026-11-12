import ContinuousFlexibility.Analysis.N05CanonicalPhysicalAE
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Change of variables for the genuine canonical chart

The coordinate determinant used by N04 is the determinant of its actual
Fréchet derivative. The change-of-variables theorem therefore applies to
the actual physical half-period tiles and their source measures. At the
controlled reference chart this determinant is the real radial derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- The coordinate formula in the frozen definition is the determinant
appearing in the measure-theoretic change of variables. -/
theorem n05_planeJacobian_eq_det (Φ : PolarPoint → PolarPoint) (p : PolarPoint) :
    planeJacobian Φ p = (fderiv ℝ Φ p).det := by
  change planeJacobian Φ p =
    LinearMap.det (fderiv ℝ Φ p : PolarPoint →ₗ[ℝ] PolarPoint)
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]
  simp only [planeJacobian, mul_comm]

/-- An angle-preserving actual chart maps the physical half-period tile
bijectively onto the frozen canonical rectangle. -/
theorem n05_canonicalChart_halfPeriod_bijOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K z m, (K.chart z m p).2 = p.2) :
    BijOn (K.chart z m)
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))
      (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
  obtain ⟨hΦ, hΨ, hleft, hright, _⟩ := h04.1.charts z hz hs m
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have hpopen : p ∈ physicalPieceOpen S K z m := hp.1
    exact ⟨(hΦ hpopen).1, by simpa only [hangle p hpopen] using hp.2.2⟩
  · intro p hp q hq he
    have hip := hleft p hp.1
    have hiq := hleft q hq.1
    exact hip.symm.trans ((congrArg (K.inverseChart z m) he).trans hiq)
  · intro p hp
    have hpopen : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    have hsecond : (K.inverseChart z m p).2 = p.2 := by
      have he := congrArg Prod.snd (hright p hpopen)
      simpa only [hangle _ (hΨ hpopen)] using he
    exact ⟨K.inverseChart z m p,
      ⟨hΨ hpopen, mem_univ _, by simpa only [hsecond] using hp.2⟩,
      hright p hpopen⟩

/-- Actual differentiability on the open piece gives the derivative required
on its half-period tile, including the angular boundary. -/
theorem n05_canonicalChart_hasFDerivWithin
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∀ p ∈ physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
      HasFDerivWithinAt (K.chart z m) (fderiv ℝ (K.chart z m) p)
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) p := by
  have hc := (h04.1.charts z hz hs m).2.2.2.2.1
  intro p hp
  exact ((hc.differentiableOn (by simp)).hasFDerivAt
    ((h04.1.domains z hz hs m).1.mem_nhds hp.1)).hasFDerivWithinAt

/-- Integrability under the actual canonical coordinate change. -/
theorem n05_canonicalChart_integrable_iff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K z m, (K.chart z m p).2 = p.2)
    (g : PolarPoint → ℝ) :
    Integrable g (canonicalMeasure S K m) ↔
      Integrable (fun p => |planeJacobian (K.chart z m) p| * g (K.chart z m p))
        (volume.restrict
          (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))) := by
  have hb := n05_canonicalChart_halfPeriod_bijOn h04 hz hs m hangle
  have he := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    ((h04.1.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))
    (n05_canonicalChart_hasFDerivWithin h04 hz hs m) hb.injOn g
  rw [hb.image_eq] at he
  simpa only [IntegrableOn, canonicalMeasure, ← n05_planeJacobian_eq_det,
    smul_eq_mul] using he

/-- The actual integral formula; no independently specified Jacobian or
pushforward measure is used. -/
theorem n05_canonicalChart_integral
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K z m, (K.chart z m p).2 = p.2)
    (g : PolarPoint → ℝ) :
    (∫ p, g p ∂canonicalMeasure S K m) =
      ∫ p, |planeJacobian (K.chart z m) p| * g (K.chart z m p)
        ∂volume.restrict
          (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) := by
  have hb := n05_canonicalChart_halfPeriod_bijOn h04 hz hs m hangle
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume
    ((h04.1.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))
    (n05_canonicalChart_hasFDerivWithin h04 hz hs m) hb.injOn g
  rw [hb.image_eq] at he
  simpa only [canonicalMeasure, ← n05_planeJacobian_eq_det, smul_eq_mul] using he

/-- The nonnegative integral formula also holds before integrability has
been established, which permits a countable disjoint-piece estimate. -/
theorem n05_canonicalChart_lintegral
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K z m, (K.chart z m p).2 = p.2)
    (g : PolarPoint → ENNReal) :
    (∫⁻ p, g p ∂canonicalMeasure S K m) =
      ∫⁻ p, ENNReal.ofReal |planeJacobian (K.chart z m) p| * g (K.chart z m p)
        ∂volume.restrict
          (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) := by
  have hb := n05_canonicalChart_halfPeriod_bijOn h04 hz hs m hangle
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    ((h04.1.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))
    (n05_canonicalChart_hasFDerivWithin h04 hz hs m) hb.injOn g
  rw [hb.image_eq] at he
  simpa only [canonicalMeasure, ← n05_planeJacobian_eq_det] using he

/-- At the controlled reference, the true planar Jacobian is exactly the
ordinary radial derivative occurring in the coordinate bounds. -/
theorem n05_reference_planeJacobian_radial
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ referencePhysicalPieceOpen S K m) :
    planeJacobian (K.chart (C.referenceState, 0) m) p =
      deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1 := by
  have h01 := h.1.1.1
  have hcActual := (h.2.2.2.2.1.charts (C.referenceState, 0)
    (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m).2.2.2.2.1
  have hc : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
      (referencePhysicalPieceOpen S K m) := by
    simpa only [h.2.2.2.2.1.referenceDomain m] using hcActual
  let ξ : ℝ → ℝ := fun r => (K.chart (C.referenceState, 0) m (r, 0)).1
  have hline : ContDiff ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hp0 : (p.1, (0 : ℝ)) ∈ referencePhysicalPieceOpen S K m :=
    ⟨hp.1, mem_univ (0 : ℝ)⟩
  have hc0 : ContDiffAt ℝ ∞ (K.chart (C.referenceState, 0) m) (p.1, 0) :=
    hc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp0)
  have hlineAt : ContDiffAt ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) p.1 :=
    hline.contDiffAt
  have hξ : DifferentiableAt ℝ ξ p.1 :=
    (hc0.comp p.1 hlineAt).fst.differentiableAt (by simp)
  have hFD : HasFDerivAt (fun q : PolarPoint => (ξ q.1, q.2))
      (((ContinuousLinearMap.toSpanSingleton ℝ (deriv ξ p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    (hξ.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hnear : K.chart (C.referenceState, 0) m =ᶠ[𝓝 p]
      (fun q : PolarPoint => (ξ q.1, q.2)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact (hcoordinates.1 m q hq).1
  rw [planeJacobian, (hFD.congr_of_eventuallyEq hnear).fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    one_mul, zero_mul, mul_one, mul_zero, sub_zero, ξ]

end ContinuousFlexibility.Statements

