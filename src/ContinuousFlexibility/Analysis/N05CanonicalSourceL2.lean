import ContinuousFlexibility.Analysis.N05CanonicalSourceL2Local
import ContinuousFlexibility.Analysis.N05PeriodicPhysicalL2Norm
import ContinuousFlexibility.Analysis.N05PhysicalPieces

/-!
# Global finite reference-source bounds from canonical volume data

The genuine physical pieces cover the annulus outside the N04 exceptional
null set. Their local square-integral estimates sum against the actual
canonical Hilbert norm. Periodicity then supplies the full reference
angular interval, with a constant independent of the finite localizer set.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem n05_volumeSource_finite_weight_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : Finset ℕ) (v : V.level γ t s) (f : PolarPoint → ℝ),
      Function.Periodic f (0, Real.pi) →
      (∀ m, (V.forget γ t s v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m f) →
      MemLp (fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) 2
        (radialPhysicalMeasure D) ∧
      (∫ p, (Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) ^ 2
        ∂radialPhysicalMeasure D) ≤ B * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hpiece⟩ :=
    n05_canonicalSource_finite_weight_piece_bound hD hT h hcoordinates hγw hgap t M
  refine ⟨2 * B, by positivity, fun q v f hf hrep => ?_⟩
  have hrepr (m : ℕ) :
      (fun p => n05CanonicalSampleWeight T S K γ t m * v.val m 0 p)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m f := by
    have hm := hrep m
    rw [hV.2.2.2 γ t s v m] at hm
    have hsmul : (n05CanonicalSampleWeight T S K γ t m • v.val m 0
        : CanonicalL2 S K m) =ᵐ[canonicalMeasure S K m]
        (fun p => n05CanonicalSampleWeight T S K γ t m * v.val m 0 p) := by
      filter_upwards [Lp.coeFn_smul (n05CanonicalSampleWeight T S K γ t m)
        (v.val m 0)] with p hp
      simpa only [Pi.smul_apply, smul_eq_mul] using hp
    exact hsmul.symm.trans hm
  let g : PolarPoint → ℝ := fun p =>
    Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p
  let U : ℕ → Set PolarPoint := fun m =>
    Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi
  have hlocal (m : ℕ) : MemLp g 2 (volume.restrict (U m)) ∧
      (∫ p, g p ^ 2 ∂volume.restrict (U m)) ≤ B * ‖v.val m 0‖ ^ 2 :=
    hpiece q m (v.val m 0) f (hrepr m)
  have hsum : Summable (fun m => ‖v.val m‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Submodule.norm_coe] using
      (lp.memℓp v.val).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hzeroBound (m : ℕ) : ‖v.val m 0‖ ^ 2 ≤ ‖v.val m‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (v.val m) 0) 2
  have hsum0 : Summable (fun m => ‖v.val m 0‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hzeroBound hsum
  have hsumI : Summable (fun m => ∫ p, g p ^ 2 ∂volume.restrict (U m)) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun m => (hlocal m).2) (hsum0.mul_left B)
  have hsumNorm : Summable (fun m => ∫ p in U m, ‖g p ^ 2‖) := by
    have hnormSq (p : PolarPoint) : ‖g p ^ 2‖ = g p ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g p))]
    simpa only [hnormSq] using hsumI
  have hsq : IntegrableOn (fun p => g p ^ 2) (⋃ m, U m) volume :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun m => (hlocal m).1.integrable_sq) hsumNorm
  have hmeas : AEStronglyMeasurable g (volume.restrict (⋃ m, U m)) :=
    AEStronglyMeasurable.iUnion (fun m => (hlocal m).1.aestronglyMeasurable)
  have hcover : (⋃ m, U m) =ᵐ[volume] (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) :=
    n05_physicalHalfPeriod_cover_ae h.2.2.2.2
  have hhalf : MemLp g 2 (volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) := by
    have hi := (memLp_two_iff_integrable_sq hmeas).mpr hsq
    rw [Measure.restrict_congr_set hcover] at hi
    exact hi
  have hperiodic : Function.Periodic g (0, Real.pi) := by
    intro p
    simp only [g, Prod.fst_add, add_zero, hf p]
  have hdisjoint : Pairwise (fun m n => Disjoint (U m) (U n)) := by
    intro m n hmn
    exact disjoint_prod.mpr (Or.inl (n05_physicalPieces_pairwise_disjoint h.2.2.2.2 hmn))
  have hhalfIntegral :
      (∫ p, g p ^ 2 ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) =
        ∑' m, ∫ p, g p ^ 2 ∂volume.restrict (U m) := by
    rw [← Measure.restrict_congr_set hcover]
    exact integral_iUnion (fun m => measurableSet_Ioo.prod measurableSet_Ioc) hdisjoint hsq
  have hnorm : (∑' m, ‖v.val m‖ ^ 2) = ‖v‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Submodule.norm_coe] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v.val).symm
  have hsum0Bound : (∑' m, ‖v.val m 0‖ ^ 2) ≤ ‖v‖ ^ 2 :=
    (Summable.tsum_le_tsum hzeroBound hsum0 hsum).trans_eq hnorm
  have hhalfBound :
      (∫ p, g p ^ 2 ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) ≤
        B * ‖v‖ ^ 2 := by
    rw [hhalfIntegral]
    calc
      _ ≤ ∑' m, B * ‖v.val m 0‖ ^ 2 :=
        Summable.tsum_le_tsum (fun m => (hlocal m).2) hsumI (hsum0.mul_left B)
      _ = B * ∑' m, ‖v.val m 0‖ ^ 2 := tsum_mul_left
      _ ≤ B * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_left hsum0Bound hB.le
  refine ⟨n05_piPeriodic_memLp_fullPeriod measurableSet_Ioo hperiodic hhalf, ?_⟩
  change (∫ p, g p ^ 2 ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) ≤ _
  dsimp only [radialCore] at hhalfBound ⊢
  rw [n05_piPeriodic_integral_sq_fullPeriod measurableSet_Ioo hperiodic hhalf]
  nlinarith only [hhalfBound]

end ContinuousFlexibility.Statements
