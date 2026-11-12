import ContinuousFlexibility.Analysis.CanonicalSourceConversion
import ContinuousFlexibility.Analysis.N05CanonicalTests
import ContinuousFlexibility.Geometry.EuclideanRigidity

/-!
# Local integrability of raw canonical representatives

An actual canonical L² source or height determines a locally integrable
physical representative on the open half-period of each piece. This is the
reverse direction of coordinate integrability: no continuity of the raw
physical function is assumed.

The proof first uses the integrability part of change of variables on a
compact physical subset. The positive height and nonzero Jacobian then
allow division by a continuous nonvanishing factor on that compact set.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- An integrable canonical pullback with a continuous nonzero physical
factor gives local physical integrability. -/
theorem n07b_locallyIntegrable_of_canonical_factor
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ)
    {a f : PolarPoint → ℝ}
    (ha : ContinuousOn a (physicalPieceOpen S K z m))
    (ha0 : ∀ p ∈ physicalPieceOpen S K z m, a p ≠ 0)
    (hf : Integrable (fun p =>
      a (K.inverseChart z m p) * f (K.inverseChart z m p)) (canonicalMeasure S K m)) :
    LocallyIntegrableOn f
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) volume := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hopen : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hsector m).1
  have hcharts := hK.charts z hz hsector m
  have hsmooth : ∀ p ∈ physicalPieceOpen S K z m,
      ContDiffAt ℝ ∞ (K.chart z m) p := fun p hp =>
    (hcharts.2.2.2.2.1 p hp).contDiffAt (hopen.mem_nhds hp)
  have hJ : ContinuousOn (planeJacobian (K.chart z m)) (physicalPieceOpen S K z m) :=
    fun p hp => (contDiffAt_planeJacobian (hsmooth p hp)).continuousAt.continuousWithinAt
  have hJ0 : ∀ p ∈ physicalPieceOpen S K z m, |planeJacobian (K.chart z m) p| ≠ 0 :=
    fun p hp => abs_ne_zero.mpr (hcharts.2.2.2.2.2.2.2 p hp).2.1
  have hnormalizer : ContinuousOn
      (fun p => (|planeJacobian (K.chart z m) p| * a p)⁻¹)
      (physicalPieceOpen S K z m) :=
    (hJ.abs.mul ha).inv₀ (fun p hp => mul_ne_zero (hJ0 p hp) (ha0 p hp))
  apply (locallyIntegrableOn_iff
    (hopen.inter (isOpen_univ.prod isOpen_Ioo)).isLocallyClosed).mpr
  intro Q hQsub hQ
  have hQphysical : Q ⊆ physicalPieceOpen S K z m := hQsub.trans inter_subset_left
  have himage := canonicalChart_image_openStrip hK hz hsector m
  have hQimage : K.chart z m '' Q ⊆
      Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi := by
    rintro p ⟨q, hq, rfl⟩
    have hmem : K.chart z m q ∈
        canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi) := by
      rw [← himage]
      exact mem_image_of_mem _ (hQsub hq)
    exact ⟨hmem.1.1, ⟨hmem.2.2.1, hmem.2.2.2.le⟩⟩
  have hfbase : IntegrableOn (fun p =>
      a (K.inverseChart z m p) * f (K.inverseChart z m p))
      (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) volume := hf
  have hd : ∀ p ∈ Q, HasFDerivWithinAt (K.chart z m)
      (fderiv ℝ (K.chart z m) p) Q p := fun p hp =>
    ((hsmooth p (hQphysical hp)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hi := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (volume : Measure PolarPoint) hQ.measurableSet hd
    ((canonicalChart_injOn hK hz hsector m).mono hQphysical)
    (fun p => a (K.inverseChart z m p) * f (K.inverseChart z m p))).mp
      (hfbase.mono_set hQimage)
  have hprod := hi.mul_continuousOn (hnormalizer.mono hQphysical) hQ
  apply hprod.congr
  filter_upwards [ae_restrict_mem hQ.measurableSet] with p hp
  change (|(fderiv ℝ (K.chart z m) p).det| *
      (a (K.inverseChart z m (K.chart z m p)) *
        f (K.inverseChart z m (K.chart z m p)))) *
      (|planeJacobian (K.chart z m) p| * a p)⁻¹ = f p
  rw [hcharts.2.2.1 p (hQphysical hp), ← planeJacobian_eq_fderiv_det]
  field_simp [hJ0 p (hQphysical hp), ha0 p (hQphysical hp)] <;> ring

/-- A source already represented by a canonical L² function is locally
integrable in the actual physical half-period piece. -/
theorem n07b_locallyIntegrable_of_canonicalSource_memLp
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {f : PolarPoint → ℝ}
    (hf : MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m)) :
    LocallyIntegrableOn f
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) volume := by
  have hcharts := hK.charts z hz hsector m
  have hopen : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hsector m).1
  have hJ : ContinuousOn (planeJacobian (K.chart z m)) (physicalPieceOpen S K z m) := by
    intro p hp
    exact (contDiffAt_planeJacobian
      ((hcharts.2.2.2.2.1 p hp).contDiffAt (hopen.mem_nhds hp))).continuousAt.continuousWithinAt
  have hJ0 : ∀ p ∈ physicalPieceOpen S K z m, |planeJacobian (K.chart z m) p| ≠ 0 :=
    fun p hp => abs_ne_zero.mpr (hcharts.2.2.2.2.2.2.2 p hp).2.1
  have hh0 : ∀ p ∈ physicalPieceOpen S K z m, K.height z m p ≠ 0 :=
    fun p hp => (hcharts.2.2.2.2.2.2.2 p hp).1.ne'
  let a : PolarPoint → ℝ := fun p => K.height z m p / |planeJacobian (K.chart z m) p|
  have ha : ContinuousOn a (physicalPieceOpen S K z m) :=
    hcharts.2.2.2.2.2.2.1.continuousOn.div₀ hJ.abs hJ0
  have ha0 : ∀ p ∈ physicalPieceOpen S K z m, a p ≠ 0 :=
    fun p hp => div_ne_zero (hh0 p hp) (hJ0 p hp)
  have hi : Integrable (fun p =>
      a (K.inverseChart z m p) * f (K.inverseChart z m p)) (canonicalMeasure S K m) := by
    apply (hf.integrable (by norm_num)).congr
    exact Eventually.of_forall (fun p => by dsimp only [canonicalSource, a]; ring)
  exact n07b_locallyIntegrable_of_canonical_factor hK hz hsector m ha ha0 hi

/-- The actual canonical height likewise supplies local integrability of
its raw physical field; no smoothness of that field is used. -/
theorem n07b_locallyIntegrable_of_canonicalHeight_memLp
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {u : PolarPoint → ℝ}
    (hu : MemLp (canonicalHeight S K z m u) 2 (canonicalMeasure S K m)) :
    LocallyIntegrableOn u
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) volume := by
  have hcharts := hK.charts z hz hsector m
  have hh0 : ∀ p ∈ physicalPieceOpen S K z m, K.height z m p ≠ 0 :=
    fun p hp => (hcharts.2.2.2.2.2.2.2 p hp).1.ne'
  let a : PolarPoint → ℝ := fun p => (K.height z m p)⁻¹
  have ha : ContinuousOn a (physicalPieceOpen S K z m) :=
    hcharts.2.2.2.2.2.2.1.continuousOn.inv₀ hh0
  have ha0 : ∀ p ∈ physicalPieceOpen S K z m, a p ≠ 0 :=
    fun p hp => inv_ne_zero (hh0 p hp)
  have hi : Integrable (fun p =>
      a (K.inverseChart z m p) * u (K.inverseChart z m p)) (canonicalMeasure S K m) := by
    apply (hu.integrable (by norm_num)).congr
    exact Eventually.of_forall (fun p => by dsimp only [canonicalHeight, a]; ring)
  exact n07b_locallyIntegrable_of_canonical_factor hK hz hsector m ha ha0 hi

/-- A canonical representation itself supplies both local integrability
inputs for the weak equation, after retaining its stored left constant. -/
theorem n07b_representation_locallyIntegrable
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (hchi : Continuous S.chiLeft)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f) (m : ℕ) :
    LocallyIntegrableOn η
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) volume ∧
    LocallyIntegrableOn f
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) volume := by
  constructor
  · have hrem := n07b_locallyIntegrable_of_canonicalHeight_memLp hK hz hsector m
      (MemLp.ae_eq (hrep.1 m) (Lp.memLp (U.1 m)))
    have hleft : Continuous (fun p : PolarPoint => U.2.1 * S.chiLeft p.1) :=
      continuous_const.mul (hchi.comp continuous_fst)
    have hopen : IsOpen
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) :=
      (hK.domains z hz hsector m).1.inter (isOpen_univ.prod isOpen_Ioo)
    have hl : LocallyIntegrableOn (fun p : PolarPoint => U.2.1 * S.chiLeft p.1)
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) volume :=
      hleft.continuousOn.locallyIntegrableOn hopen.measurableSet
    have heq : (fun p => η p - U.2.1 * S.chiLeft p.1) +
        (fun p => U.2.1 * S.chiLeft p.1) = η := by
      funext p
      change (η p - U.2.1 * S.chiLeft p.1) + U.2.1 * S.chiLeft p.1 = η p
      exact sub_add_cancel _ _
    rw [← heq]
    exact hrem.add hl
  · exact n07b_locallyIntegrable_of_canonicalSource_memLp hK hz hsector m
      (MemLp.ae_eq (hrep.2 m) (Lp.memLp (F m)))

end ContinuousFlexibility.Analysis
