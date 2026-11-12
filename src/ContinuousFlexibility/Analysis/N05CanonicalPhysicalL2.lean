import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Analysis.N05CanonicalPhysicalL2Local
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Canonical volume membership implies the actual physical endpoint L² class

The prescribed sample weights, genuine coordinate Jacobians, and countable
physical-piece cover convert the canonical Hilbert square sum into physical
inverse-square-root profile integrability. Periodicity supplies the second
half of the physical angular interval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- An actual π-periodic function in L² on the canonical half-period lies
in L² on the full physical angular period. -/
theorem n05_piPeriodic_memLp_fullPeriod
    {J : Set ℝ} (hJ : MeasurableSet J) {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi))
    (hhalf : MemLp f 2 (volume.restrict (J ×ˢ Ioc (0 : ℝ) Real.pi))) :
    MemLp f 2 (volume.restrict (J ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hshift := hhalf.comp_measurePreserving
    ((measurePreserving_sub_right volume ((0, Real.pi) : PolarPoint)).restrict_preimage
      (hJ.prod measurableSet_Ioc))
  have hsub : J ×ˢ Ioc Real.pi (2 * Real.pi) ⊆
      (fun p : PolarPoint => p - (0, Real.pi)) ⁻¹' (J ×ˢ Ioc (0 : ℝ) Real.pi) := by
    intro p hp
    constructor
    · simpa using hp.1
    · change 0 < p.2 - Real.pi ∧ p.2 - Real.pi ≤ Real.pi
      constructor <;> linarith only [hp.2.1, hp.2.2]
  have hupperShift := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hshift
  have hupper : MemLp f 2 (volume.restrict (J ×ˢ Ioc Real.pi (2 * Real.pi))) := by
    apply MemLp.ae_eq _ hupperShift
    exact Eventually.of_forall fun p => n05_piPeriodic_sub hf p
  have hmeas : AEStronglyMeasurable f
      (volume.restrict
        ((J ×ˢ Ioc (0 : ℝ) Real.pi) ∪ (J ×ˢ Ioc Real.pi (2 * Real.pi)))) :=
    aestronglyMeasurable_union_iff.mpr
      ⟨hhalf.aestronglyMeasurable, hupper.aestronglyMeasurable⟩
  have hint : IntegrableOn (fun p => f p ^ 2)
      ((J ×ˢ Ioc (0 : ℝ) Real.pi) ∪ (J ×ˢ Ioc Real.pi (2 * Real.pi))) volume :=
    integrableOn_union.mpr ⟨hhalf.integrable_sq, hupper.integrable_sq⟩
  have hunion := (memLp_two_iff_integrable_sq hmeas).mpr hint
  simpa only [← prod_union, Ioc_union_Ioc_eq_Ioc Real.pi_pos.le
    (show Real.pi ≤ 2 * Real.pi by linarith [Real.pi_pos])] using hunion

/-- The actual N04 null exceptional cover is also a null exceptional cover
for the physical half-period rectangle. -/
theorem n05_physicalHalfPeriod_cover_ae
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε) :
    (⋃ m, Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)
      =ᵐ[volume] (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) := by
  have hpieces := h04.1.referenceBounds
  obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
  have hEplane : ∀ᵐ p : PolarPoint ∂volume, p.1 ∉ E := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae (measure_eq_zero_iff_ae_notMem.mp hE)
  filter_upwards [hEplane] with p hpE
  apply propext
  constructor
  · intro hp
    obtain ⟨m, hm⟩ := mem_iUnion.mp hp
    exact ⟨(hpieces m).2.2 hm.1, hm.2⟩
  · intro hp
    obtain ⟨m, hm, _⟩ := hcover p.1 ⟨hp.1, hpE⟩
    exact mem_iUnion.mpr ⟨m, hm, hp.2⟩

/-- Any actual canonical volume model, at every positive endpoint exponent,
forces the represented periodic height into the physical endpoint class.
No physical integrability, measurability, or change-of-measure estimate is
added as a premise. -/
theorem n05_volumeMember_canonicalHeight_endpoint_memLp
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {s : ℕ} (hγ : 0 < γ) {W : CanonicalSequence S K}
    (hW : VolumeMember S K V γ t s W) {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi))
    (hrep : ∀ m, (W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m f) :
    MemLp (fun p => Real.sqrt ((D.w p.1)⁻¹) * f p) 2 (radialPhysicalMeasure D) := by
  obtain ⟨v, hv⟩ := hW
  obtain ⟨B, hB, hpiece⟩ :=
    n05_canonicalHeight_endpoint_piece_bound hD hT h hcoordinates hγ t
  have hrepr (m : ℕ) :
      (fun p => n05CanonicalSampleWeight T S K γ t m * v.val m 0 p)
        =ᵐ[canonicalMeasure S K m] canonicalHeight S K (C.referenceState, 0) m f := by
    have hformula : W m = n05CanonicalSampleWeight T S K γ t m • v.val m 0 := by
      exact (congrFun hv m).symm.trans (hV.2.2.2 γ t s v m)
    have hm := hrep m
    rw [hformula] at hm
    have hsmul : (n05CanonicalSampleWeight T S K γ t m • v.val m 0
        : CanonicalL2 S K m) =ᵐ[canonicalMeasure S K m]
        (fun p => n05CanonicalSampleWeight T S K γ t m * v.val m 0 p) := by
      filter_upwards [Lp.coeFn_smul
        (n05CanonicalSampleWeight T S K γ t m) (v.val m 0)] with p hp
      simpa only [Pi.smul_apply, smul_eq_mul] using hp
    exact hsmul.symm.trans hm
  let q : PolarPoint → ℝ := fun p => Real.sqrt ((D.w p.1)⁻¹) * f p
  let U : ℕ → Set PolarPoint := fun m =>
    Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi
  have hlocal (m : ℕ) : MemLp q 2 (volume.restrict (U m)) ∧
      (∫ p, q p ^ 2 ∂volume.restrict (U m)) ≤ B * ‖v.val m 0‖ ^ 2 :=
    hpiece m (v.val m 0) f (hrepr m)
  have hsum : Summable (fun m => ‖v.val m‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp v.val).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hsum0 : Summable (fun m => ‖v.val m 0‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun m => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (v.val m) 0) 2) hsum
  have hsumI : Summable (fun m => ∫ p, q p ^ 2 ∂volume.restrict (U m)) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun m => (hlocal m).2) (hsum0.mul_left B)
  have hsumNorm : Summable (fun m => ∫ p in U m, ‖q p ^ 2‖) := by
    simpa only [Real.norm_eq_abs, abs_sq] using hsumI
  have hsq : IntegrableOn (fun p => q p ^ 2) (⋃ m, U m) volume :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun m => (hlocal m).1.integrable_sq) hsumNorm
  have hmeas : AEStronglyMeasurable q (volume.restrict (⋃ m, U m)) :=
    AEStronglyMeasurable.iUnion (fun m => (hlocal m).1.aestronglyMeasurable)
  have hcover := n05_physicalHalfPeriod_cover_ae h.2.2.2.2.1
  have hhalf : MemLp q 2 (volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) := by
    have hlocalUnion := (memLp_two_iff_integrable_sq hmeas).mpr hsq
    change MemLp q 2 (volume.restrict
      (⋃ m, Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi))
      at hlocalUnion
    rw [Measure.restrict_congr_set hcover] at hlocalUnion
    exact hlocalUnion
  have hperiodic : Function.Periodic q (0, Real.pi) := by
    intro p
    have he : f (p + (0, Real.pi)) = f p := hf p
    have hfst : (p + ((0, Real.pi) : PolarPoint)).1 = p.1 := add_zero p.1
    change Real.sqrt ((D.w (p + (0, Real.pi)).1)⁻¹) * f (p + (0, Real.pi)) =
      Real.sqrt ((D.w p.1)⁻¹) * f p
    rw [hfst, he]
  exact n05_piPeriodic_memLp_fullPeriod measurableSet_Ioo hperiodic hhalf

end ContinuousFlexibility.Statements
