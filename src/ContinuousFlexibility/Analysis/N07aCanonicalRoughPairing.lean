import ContinuousFlexibility.Analysis.N07aCanonicalHalfStrip
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Rough pairing through the actual canonical chart

The reflected periodic chart preserves the actual half-period cell. The
ordinary plane change-of-variables theorem therefore extends the original
smooth pairing identity to arbitrary representatives, with an exact
integrability equivalence. No regularity of the unknown is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Module
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n07a_planeJacobian_eq_det (F : PolarPoint → PolarPoint) (p : PolarPoint) :
    planeJacobian F p = (fderiv ℝ F p).det := by
  change planeJacobian F p = LinearMap.det (fderiv ℝ F p).toLinearMap
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Basis.finTwoProd_zero, Basis.finTwoProd_one,
    Basis.coe_finTwoProd_repr, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.coe_coe, planeJacobian]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

private theorem n07a_canonical_half_geometry
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    let Q := Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi
    (K.chart z m '' Q = Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
    InjOn (K.chart z m) Q ∧
    (∀ p ∈ Q, HasFDerivWithinAt (K.chart z m) (fderiv ℝ (K.chart z m) p) Q p) ∧
    (∀ p ∈ Q, K.inverseChart z m (K.chart z m p) = p ∧
      K.height z m p ≠ 0 ∧ planeJacobian (K.chart z m) p ≠ 0) := by
  rcases h04 with ⟨_, _, _, _, _, _, _, hgeom, _, href, hiref, _⟩
  obtain ⟨hf, hg, hgf, hfg, hfs, hgs, _, hgp⟩ := hgeom z hz hs m
  have hfr : ∀ p ∈ physicalPieceOpen S K m,
      K.chart z m (p.1, -p.2) = ((K.chart z m p).1, -(K.chart z m p).2) :=
    fun p hp => (href z hz hs m p hp).1
  have hfp : ∀ p ∈ physicalPieceOpen S K m,
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) :=
    fun p hp => (hgp p hp).2.2.1
  refine ⟨n07a_strip_image_half hf hg hgf hfg hfs hgs hfr (hiref z hz hs m) hfp,
    ?_, ?_, ?_⟩
  · intro p hp q hq he
    exact (hgf p ⟨hp.1, mem_univ _⟩).symm.trans
      ((congrArg (K.inverseChart z m) he).trans (hgf q ⟨hq.1, mem_univ _⟩))
  · intro p hp
    exact ((hfs.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hp.1, mem_univ _⟩)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · intro p hp
    have hp' : p ∈ physicalPieceOpen S K m := ⟨hp.1, mem_univ _⟩
    exact ⟨hgf p hp', (hgp p hp').1.ne', (hgp p hp').2.1⟩

private theorem n07a_canonical_pairing_cancel (m : ℕ) (u f : PolarPoint → ℝ)
    {p : PolarPoint} (hinv : K.inverseChart z m (K.chart z m p) = p)
    (hh : K.height z m p ≠ 0) (hj : planeJacobian (K.chart z m) p ≠ 0) :
    |(fderiv ℝ (K.chart z m) p).det| •
      (canonicalHeight S K z m u (K.chart z m p) *
        canonicalSource S K z m f (K.chart z m p)) = u p * f p := by
  rw [← n07a_planeJacobian_eq_det]
  simp only [canonicalHeight, canonicalSource, hinv, smul_eq_mul]
  field_simp [hh, abs_ne_zero.mpr hj]

/-- The geometric pairing is valid for arbitrary actual functions, including
the rough representatives in the reference and perturbed graph relations. -/
theorem n07a_canonical_pairing_all
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (u f : PolarPoint → ℝ) :
    (∫ p in Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi,
      u p * f p) =
    ∫ p, canonicalHeight S K z m u p * canonicalSource S K z m f p
      ∂canonicalMeasure S K m := by
  obtain ⟨himage, hinj, hderiv, hpoint⟩ := n07a_canonical_half_geometry h04 hz hs m
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_Ioo.prod measurableSet_Ioc) hderiv hinj
    (fun p => canonicalHeight S K z m u p * canonicalSource S K z m f p)
  rw [himage] at hcov
  unfold canonicalMeasure
  rw [hcov]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioc)
  intro p hp
  have h := hpoint p hp
  exact (n07a_canonical_pairing_cancel m u f h.1 h.2.1 h.2.2).symm

/-- The same actual chart equivalence preserves integrability of the paired
functions; this permits Fubini for weak equations without a smooth unknown. -/
theorem n07a_canonical_pairing_integrable_iff
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (u f : PolarPoint → ℝ) :
    Integrable (fun p => canonicalHeight S K z m u p * canonicalSource S K z m f p)
      (canonicalMeasure S K m) ↔
    IntegrableOn (fun p => u p * f p)
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
  obtain ⟨himage, hinj, hderiv, hpoint⟩ := n07a_canonical_half_geometry h04 hz hs m
  have hcov := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_Ioo.prod measurableSet_Ioc) hderiv hinj
    (fun p => canonicalHeight S K z m u p * canonicalSource S K z m f p)
  rw [himage] at hcov
  apply hcov.trans
  apply integrable_congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  have h := hpoint p hp
  exact n07a_canonical_pairing_cancel m u f h.1 h.2.1 h.2.2

end ContinuousFlexibility.Analysis
