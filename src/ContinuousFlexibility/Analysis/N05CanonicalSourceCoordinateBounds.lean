import ContinuousFlexibility.Analysis.N05CanonicalSourceEmbedding

/-!
# Source bounds for every square-summable canonical coordinate family

The actual source-density estimate applies to an arbitrary canonical L²
coordinate. Summing it over the disjoint physical pieces gives the same
fixed reference material order for every angular jet. No reflection
projection or zero-jet restriction enters this estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ)

include hD hT h hcoordinates hγw hgap in
/-- The constant precedes the canonical family and the finite localizer
set. The full-period estimate includes exactly the half-period factor 2. -/
theorem n05_canonicalSequenceSource_finite_weight_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : Finset ℕ) (a : CanonicalL2Sequence S K)
      (f : PolarPoint → ℝ), Function.Periodic f (0, Real.pi) →
      (∀ m, (fun p => n05CanonicalSampleWeight T S K γ t m * a m p)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m f) →
      MemLp (fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) 2
        (radialPhysicalMeasure D) ∧
      (∫ p, (Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) ^ 2
        ∂radialPhysicalMeasure D) ≤ B * ‖a‖ ^ 2 := by
  obtain ⟨B, hB, hpiece⟩ :=
    n05_canonicalSource_finite_weight_piece_bound hD hT h hcoordinates hγw hgap t M
  refine ⟨2 * B, by positivity, fun q a f hf hrep => ?_⟩
  let g : PolarPoint → ℝ := fun p =>
    Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p
  let U : ℕ → Set PolarPoint := fun m =>
    Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi
  have hlocal (m : ℕ) : MemLp g 2 (volume.restrict (U m)) ∧
      (∫ p, g p ^ 2 ∂volume.restrict (U m)) ≤ B * ‖a m‖ ^ 2 :=
    hpiece q m (a m) f (hrep m)
  have hsum : Summable (fun m => ‖a m‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp a).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hsumI : Summable (fun m => ∫ p, g p ^ 2 ∂volume.restrict (U m)) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun m => (hlocal m).2) (hsum.mul_left B)
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
  have hnorm : (∑' m, ‖a m‖ ^ 2) = ‖a‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) a).symm
  have hhalfBound :
      (∫ p, g p ^ 2 ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi)) ≤
        B * ‖a‖ ^ 2 := by
    rw [hhalfIntegral]
    calc
      _ ≤ ∑' m, B * ‖a m‖ ^ 2 :=
        Summable.tsum_le_tsum (fun m => (hlocal m).2) hsumI (hsum.mul_left B)
      _ = B * ∑' m, ‖a m‖ ^ 2 := tsum_mul_left
      _ = B * ‖a‖ ^ 2 := by rw [hnorm]
  refine ⟨n05_piPeriodic_memLp_fullPeriod measurableSet_Ioo hperiodic hhalf, ?_⟩
  change (∫ p, g p ^ 2 ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) ≤ _
  dsimp only [radialCore] at hhalfBound ⊢
  rw [n05_piPeriodic_integral_sq_fullPeriod measurableSet_Ioo hperiodic hhalf]
  nlinarith only [hhalfBound]

include hD hT h hcoordinates hγw hgap in
/-- The finite estimates give genuine cellwise L² membership and the full
source square sum, uniformly for arbitrary canonical coordinate families. -/
theorem n05_canonicalSequenceSource_reference_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (a : CanonicalL2Sequence S K) (f : PolarPoint → ℝ),
      Function.Periodic f (0, Real.pi) →
      (∀ m, (fun p => n05CanonicalSampleWeight T S K γ t m * a m p)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m f) →
      SourceDerivativeMember D γw M f ∧ sourceNormSquare D γw M (f, 0) ≤ B * ‖a‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05_canonicalSequenceSource_finite_weight_bound hD hT h hcoordinates hγw hgap t M
  refine ⟨(2 * Real.pi)⁻¹ * B, by positivity, fun a f hf hrep => ?_⟩
  have hlocal : ∀ q : Finset ℕ,
      MemLp (fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p)
        2 (radialPhysicalMeasure D) := fun q => (hb q a f hf hrep).1
  have hcell : RadialCellIntegrable D f :=
    n05_radialCellIntegrable_of_finiteSourceWeights hD.choose_spec.2.1 γw M hlocal
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hfinite (q : Finset ℕ) :
      (∑ j ∈ q, sourceCellSquare D γw M f j) ≤ ((2 * Real.pi)⁻¹ * B) * ‖a‖ ^ 2 := by
    rw [n05_finiteSourceNormSquare_eq hab γw M hcell q]
    calc
      _ ≤ (2 * Real.pi)⁻¹ * (B * ‖a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hb q a f hf hrep).2 (by positivity)
      _ = _ := (mul_assoc _ _ _).symm
  have hs : Summable (sourceCellSquare D γw M f) :=
    summable_of_sum_le (sourceCellSquare_nonneg hab γw M hcell) hfinite
  have hnorm : (∑' j, sourceCellSquare D γw M f j) ≤
      ((2 * Real.pi)⁻¹ * B) * ‖a‖ ^ 2 :=
    Real.tsum_le_of_sum_le (sourceCellSquare_nonneg hab γw M hcell) hfinite
  refine ⟨⟨hcell, hs⟩, ?_⟩
  simpa only [sourceNormSquare, zero_pow (by decide : 2 ≠ 0), zero_add] using hnorm

end ContinuousFlexibility.Statements
