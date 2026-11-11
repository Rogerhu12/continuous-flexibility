import ContinuousFlexibility.Analysis.N07bCanonicalAEPullback
import ContinuousFlexibility.Analysis.N07bDivergenceTests
import ContinuousFlexibility.Analysis.N07bRawRepresentationIntegrability

/-!
# The physical weak relation determines its canonical source

Two raw witnesses for the same canonical unknown agree a.e. on the physical
half-period of every piece. Compact planar tests can be placed in that half
period and extended to the actual full-period test class. Locality of the
divergence operator then cancels the unknown terms. Distributional separation
identifies the source witnesses and hence the actual canonical L² rows.

This proves source uniqueness for the repaired full-period N06 relation.
It does not assert that a current smooth solution belongs to the reference
closed graph; that domain inclusion is a separate analytic obligation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- The actual physical weak relation has at most one canonical source for
each fixed canonical unknown. No coefficient regularity or integrability
of the unknown pairings is required. -/
theorem n07b_perturbedCanonicalRelation_right_unique
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (hab : D.a ≤ D.b)
    {U : CanonicalUnknown S K} {F G : CanonicalSequence S K}
    (hF : PerturbedCanonicalRelation D S C K L z U F)
    (hG : PerturbedCanonicalRelation D S C K L z U G) : F = G := by
  obtain ⟨η, f, hηrep, _, hηweak⟩ := hF
  obtain ⟨ξ, g, hξrep, _, hξweak⟩ := hG
  funext m
  apply Lp.ext
  let A : Set PolarPoint :=
    physicalPieceOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)
  have hopen : IsOpen A :=
    (isOpen_Ioo.prod isOpen_univ).inter (isOpen_univ.prod isOpen_Ioo)
  have hA : A ⊆ radialCore D ×ˢ Ioo (0 : ℝ) Real.pi := by
    intro p hp
    exact ⟨(hK.2.2.2.1 m).2.2 hp.1.1, hp.2.2⟩
  have hfLoc : LocallyIntegrableOn f A volume :=
    n07b_locallyIntegrable_of_canonicalSource_memLp hK hz hsector m
      (MemLp.ae_eq (hηrep.2 m) (Lp.memLp (F m)))
  have hgLoc : LocallyIntegrableOn g A volume :=
    n07b_locallyIntegrable_of_canonicalSource_memLp hK hz hsector m
      (MemLp.ae_eq (hξrep.2 m) (Lp.memLp (G m)))
  have hrem := (n07b_canonicalHeight_ae_iff hK hz hsector m
      (fun p => η p - U.2.1 * S.chiLeft p.1)
      (fun p => ξ p - U.2.1 * S.chiLeft p.1)).mp
    ((hηrep.1 m).symm.trans (hξrep.1 m))
  have hηξbig : η =ᵐ[volume.restrict
      (physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))] ξ := by
    filter_upwards [hrem] with p hp
    exact (sub_left_inj).mp hp
  have hηξ : η =ᵐ[volume.restrict A] ξ :=
    ae_restrict_of_ae_restrict_of_subset
      (fun p hp => ⟨hp.1, ⟨hp.2.1, ⟨hp.2.2.1, hp.2.2.2.le⟩⟩⟩) hηξbig
  have hsource : f =ᵐ[volume.restrict A] g := by
    apply n07b_ae_eq_of_halfPeriod_pairing hab hopen hA hfLoc hgLoc
    intro φ hφ hcompact hs
    have htest := n07bFullPeriodTest_radialTest hφ hcompact (hs.trans hA)
    have hη := hηweak (n07bFullPeriodTest φ) htest
    have hξ := hξweak (n07bFullPeriodTest φ) htest
    have hunknown :
        (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          η (r, θ) * divergenceOperator (L.coefficients z)
            (n07bFullPeriodTest φ) (r, θ))) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          ξ (r, θ) * divergenceOperator (L.coefficients z)
            (n07bFullPeriodTest φ) (r, θ)) := by
      apply Radial.r11b_iteratedAngularMean_congr_ae hab
      have hsupport : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) Real.pi :=
        fun p hp => ⟨mem_univ _, (hA (hs hp)).2⟩
      have hmeasure : radialPhysicalMeasure D =
          volume.restrict (radialCore D ×ˢ Ioo (0 : ℝ) (2 * Real.pi)) :=
        Measure.restrict_congr_set
          (Measure.set_prod_ae_eq EventuallyEq.rfl Ioo_ae_eq_Ioc.symm)
      have hmem : ∀ᵐ p ∂radialPhysicalMeasure D,
          p ∈ radialCore D ×ˢ Ioo (0 : ℝ) (2 * Real.pi) := by
        rw [hmeasure]
        exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
      have he : ∀ᵐ p ∂volume, p ∈ A → η p = ξ p :=
        (ae_restrict_iff' hopen.measurableSet).mp hηξ
      have hefull : ∀ᵐ p ∂radialPhysicalMeasure D, p ∈ A → η p = ξ p :=
        ae_restrict_of_ae he
      filter_upwards [hmem, hefull] with p hp he
      change η p * divergenceOperator (L.coefficients z) (n07bFullPeriodTest φ) p =
        ξ p * divergenceOperator (L.coefficients z) (n07bFullPeriodTest φ) p
      rw [n07b_fullPeriodTest_divergence_eqOn (L.coefficients z) hsupport
        ⟨mem_univ _, hp.2⟩]
      by_cases hpA : p ∈ A
      · rw [he hpA]
      · have hd0 : divergenceOperator (L.coefficients z) φ p = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h =>
            hpA (hs (n07b_tsupport_divergenceOperator_subset (L.coefficients z) φ h)))
        rw [hd0, mul_zero, mul_zero]
    rw [hunknown] at hη
    exact hη.symm.trans hξ
  have hmeasure :
      volume.restrict (physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) =
        volume.restrict A := by
    simpa only [A, physicalPieceOpen, prod_inter_prod, inter_univ, univ_inter] using
      Measure.restrict_congr_set
        (polarStrip_Ioc_ae_eq_Ioo (K.physicalLeft m) (K.physicalRight m) 0 Real.pi)
  have hphysical : f =ᵐ[volume.restrict
      (physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi))] g := by
    rw [hmeasure]
    exact hsource
  have hcanonical := (n07b_canonicalSource_ae_iff hK hz hsector m f g).mpr hphysical
  exact (hηrep.2 m).trans (hcanonical.trans (hξrep.2 m).symm)

/-- N06's operator is the unique volume element realizing a given physical
weak source for an already specified member of the fixed graph. -/
theorem n07b_relativeOperator_eq_of_physical_relation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {L : ReturnCorrectionData S}
    {V : VolumeModelData S K} {b base : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
    (hK : N04PartA D S C K base ε) (hV : IsVolumeModel T S K V)
    (h06 : N06Properties D S C K L V b B P base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (hab : D.a ≤ D.b)
    (u : B.Space) (F : V.level (3 / 4 : ℝ) 0 b)
    (hF : PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b F)) : P.operator z u = F := by
  apply hV.2.2.1 (3 / 4 : ℝ) 0 b
  exact n07b_perturbedCanonicalRelation_right_unique hK hz hsector hab
    ((h06.2 z hz hsector).1 u) hF

end ContinuousFlexibility.Analysis
