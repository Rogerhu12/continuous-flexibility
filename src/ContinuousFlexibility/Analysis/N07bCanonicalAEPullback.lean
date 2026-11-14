module

public import ContinuousFlexibility.Analysis.CanonicalSourceConversion

/-!
# Almost-everywhere transport through the actual canonical charts

A differentiable inverse sends null sets to null sets. Together with the
already established image of the fundamental angular strip, this identifies
the physical a.e. class represented by a canonical source or height. The
represented functions themselves need not be measurable, continuous, or
integrable.

This is a local statement on each physical piece. It does not assert
membership in the fixed reference graph or weighted bounds across pieces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- A differentiable left inverse transports a.e. statements back through a
map. No differentiability or measurability of the represented predicate is
required. -/
theorem n07b_ae_pullback_of_differentiable_leftInverse
    {A B : Set PolarPoint} {F G : PolarPoint → PolarPoint}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hF : MapsTo F A B) (hGF : ∀ x ∈ A, G (F x) = x)
    (hG : DifferentiableOn ℝ G B) {P : PolarPoint → Prop}
    (hP : ∀ᵐ y ∂volume.restrict B, P y) :
    ∀ᵐ x ∂volume.restrict A, P (F x) := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hbad : volume ({y | ¬ P y} ∩ B) = 0 := by
    rw [← Measure.restrict_apply' hB]
    exact ae_iff.mp hP
  have himage : volume (G '' ({y | ¬ P y} ∩ B)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (volume : Measure PolarPoint) (hG.mono inter_subset_right) hbad
  apply ae_iff.mpr
  rw [Measure.restrict_apply' hA]
  apply measure_mono_null _ himage
  intro x hx
  exact ⟨F x, ⟨hx.1, hF hx.2⟩, hGF x hx.2⟩

/-- Composition with the actual inverse chart preserves and reflects a.e.
equality between raw physical functions on the fundamental strip. -/
theorem n07b_ae_inverseChart_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (u v : PolarPoint → ℝ) :
    ((fun p => u (K.inverseChart z m p)) =ᵐ[canonicalMeasure S K m]
      (fun p => v (K.inverseChart z m p))) ↔
    u =ᵐ[volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))] v := by
  let A : Set PolarPoint :=
    physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)
  let B : Set PolarPoint :=
    canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)
  have hphysicalOpen : IsOpen (physicalPieceOpen S K z m) :=
    (hK.domains z hz hsector m).1
  have hA : MeasurableSet A :=
    (hphysicalOpen.inter (isOpen_univ.prod isOpen_Ioo)).measurableSet
  have hB : MeasurableSet B :=
    ((isOpen_Ioo.prod isOpen_univ).inter (isOpen_univ.prod isOpen_Ioo)).measurableSet
  have hphysical :
      volume.restrict (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) =
        volume.restrict A := by
    exact Measure.restrict_congr_set
      (polarDomain_Ioc_ae_eq_Ioo (physicalPieceOpen S K z m) 0 Real.pi)
  have hcanonical : canonicalMeasure S K m = volume.restrict B := by
    simpa only [canonicalMeasure, B, canonicalOpen, prod_inter_prod,
      inter_univ, univ_inter] using
      Measure.restrict_congr_set
        (polarStrip_Ioc_ae_eq_Ioo (K.left m) (K.right m) 0 Real.pi)
  have hcharts := hK.charts z hz hsector m
  have himage : K.chart z m '' A = B :=
    canonicalChart_image_openStrip hK hz hsector m
  have hF : MapsTo (K.chart z m) A B := by
    intro p hp
    rw [← himage]
    exact mem_image_of_mem _ hp
  have hG : MapsTo (K.inverseChart z m) B A := by
    intro p hp
    have hpimage : p ∈ K.chart z m '' A := by rw [himage]; exact hp
    obtain ⟨q, hq, rfl⟩ := hpimage
    rw [hcharts.2.2.1 q hq.1]
    exact hq
  have hFd : DifferentiableOn ℝ (K.chart z m) A :=
    (hcharts.2.2.2.2.1.differentiableOn (by simp)).mono inter_subset_left
  have hGd : DifferentiableOn ℝ (K.inverseChart z m) B :=
    (hcharts.2.2.2.2.2.1.differentiableOn (by simp)).mono inter_subset_left
  rw [hcanonical, hphysical]
  constructor
  · intro huv
    have h := n07b_ae_pullback_of_differentiable_leftInverse hA hB hF
      (fun p hp => hcharts.2.2.1 p hp.1) hGd huv
    filter_upwards [h, ae_restrict_mem hA] with p hp hpA
    simpa only [hcharts.2.2.1 p hpA.1] using hp
  · intro huv
    exact n07b_ae_pullback_of_differentiable_leftInverse hB hA hG
      (fun p hp => hcharts.2.2.2.1 p hp.1) hFd huv

/-- The positive height factor and nonzero Jacobian do not change the a.e.
equivalence class detected by a canonical source. -/
theorem n07b_canonicalSource_ae_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (f g : PolarPoint → ℝ) :
    canonicalSource S K z m f =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m g ↔
    f =ᵐ[volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))] g := by
  rw [← n07b_ae_inverseChart_iff hK hz hsector m f g]
  have hcharts := hK.charts z hz hsector m
  have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  constructor
  · intro h
    filter_upwards [h, hmem] with p hp hpB
    have hpopen : p ∈ canonicalOpen S K m := ⟨hpB.1, mem_univ _⟩
    have hpin := hcharts.2.1 hpopen
    have hnonzero := hcharts.2.2.2.2.2.2.2 _ hpin
    have hh : K.height z m (K.inverseChart z m p) ≠ 0 := hnonzero.1.ne'
    have hJ : |planeJacobian (K.chart z m) (K.inverseChart z m p)| ≠ 0 :=
      abs_ne_zero.mpr hnonzero.2.1
    dsimp only [canonicalSource] at hp
    exact mul_left_cancel₀ hh ((div_left_inj' hJ).mp hp)
  · intro h
    filter_upwards [h] with p hp
    dsimp only [canonicalSource]
    rw [hp]

/-- The physical a.e. class is likewise recovered from its canonical height. -/
theorem n07b_canonicalHeight_ae_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (u v : PolarPoint → ℝ) :
    canonicalHeight S K z m u =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m v ↔
    u =ᵐ[volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))] v := by
  rw [← n07b_ae_inverseChart_iff hK hz hsector m u v]
  have hcharts := hK.charts z hz hsector m
  have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  constructor
  · intro h
    filter_upwards [h, hmem] with p hp hpB
    have hpopen : p ∈ canonicalOpen S K m := ⟨hpB.1, mem_univ _⟩
    have hpin := hcharts.2.1 hpopen
    have hh : K.height z m (K.inverseChart z m p) ≠ 0 :=
      (hcharts.2.2.2.2.2.2.2 _ hpin).1.ne'
    exact (div_left_inj' hh).mp hp
  · intro h
    filter_upwards [h] with p hp
    dsimp only [canonicalHeight]
    rw [hp]

/-- Two witnesses of the same canonical representation agree a.e. on each
physical piece for both the source and the physical field. -/
theorem n07b_representation_physical_ae
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {η ξ f g : PolarPoint → ℝ}
    (hη : HasCanonicalRepresentation D S C K z U F η f)
    (hξ : HasCanonicalRepresentation D S C K z U F ξ g) (m : ℕ) :
    η =ᵐ[volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))] ξ ∧
    f =ᵐ[volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))] g := by
  constructor
  · have h := (n07b_canonicalHeight_ae_iff hK hz hsector m
        (fun p => η p - U.2.1 * S.chiLeft p.1)
        (fun p => ξ p - U.2.1 * S.chiLeft p.1)).mp
      ((hη.1 m).symm.trans (hξ.1 m))
    filter_upwards [h] with p hp
    exact (sub_left_inj).mp hp
  · exact (n07b_canonicalSource_ae_iff hK hz hsector m f g).mp
      ((hη.2 m).symm.trans (hξ.2 m))

end ContinuousFlexibility.Analysis
