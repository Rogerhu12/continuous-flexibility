import ContinuousFlexibility.Analysis.N07aAngularReferenceC1
import ContinuousFlexibility.Analysis.N07aAngularReferenceCandidateBounds
import ContinuousFlexibility.Analysis.N07aAngularReferenceNaturalGraph
import ContinuousFlexibility.Analysis.N07aAngularNormalizationTransport

/-!
# Every normalized physical candidate has a genuine natural reference realization

The field is reconstructed from the actual current and reference charts.
Its first jets match at every original interface, its physical differential
source has the genuine compatibility integral, and all real natural cell
weights follow from the strict material height margin.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_referenceTransport_row_of_pieces
    (hab : D.a ≤ D.b) (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (aL : ℝ) {η v : PolarPoint → ℝ}
    (hηπ : Function.Periodic η (0, Real.pi))
    (hvπ : Function.Periodic v (0, Real.pi))
    (hv : ∀ m, EqOn v (n07aReferencePieceHeight C K z (K.inverseChart z) aL η m)
      (referencePhysicalPieceOpen S K m)) : referenceRow D v = referenceRow D η := by
  have heq : v =ᵐ[radialPhysicalMeasure D] n07bReferencePullback C K z aL η := by
    obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
    have hr : ∀ᵐ r : ℝ ∂volume, r ∉ E := by
      apply ae_iff.mpr
      simpa only [not_not, setOf_mem_eq] using hE
    have houtside : ∀ᵐ p : PolarPoint ∂volume, p.1 ∉ E := by
      rw [Measure.volume_eq_prod]
      exact (Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae hr
    change ∀ᵐ p ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)),
      v p = n07bReferencePullback C K z aL η p
    apply (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioc)).mpr
    filter_upwards [houtside] with p hpE hpstrip
    obtain ⟨m, hm, _⟩ := hcover p.1 ⟨hpstrip.1, hpE⟩
    have hp : p ∈ referencePhysicalPieceOpen S K m := ⟨hm, mem_univ _⟩
    rw [hv m hp, n07bReferencePullback_on_piece h04.1 z aL η hp]
    dsimp only [n07aReferencePieceHeight, n07bReferencePiecePullback, canonicalHeight]
    ring
  exact (n07b_referenceRow_congr_ae hab heq).trans
    (n07bReferencePullback_referenceRow h04.1 hz hs aL η)

theorem n07a_exists_referenceGraph_of_current_heightPair
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hborder : RadialTrueBorder D)
    (hrad : CanonicalGeometry.ReferenceRadial S C K)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) (μ γ M₀ M₁ : ℝ) (hγ : 0 < γ) (hγhi : γ < (3 / 4 : ℝ))
    (hrow : referenceRow D (heightPairField S u) = 0) :
    ∃ v : PolarPoint → ℝ, ContDiffOn ℝ 1 v (annularOpen D) ∧
      (∀ m, EqOn v
        (n07aReferencePieceHeight C K (liftSectorParameter S C z)
          (K.inverseChart (liftSectorParameter S C z)) u.2 (heightPairField S u) m)
        (referencePhysicalPieceOpen S K m)) ∧
      (∀ m, EqOn
        (canonicalHeight S K (C.referenceState, 0) m (fun p => v p - u.2 * S.chiLeft p.1))
        (canonicalHeight S K (liftSectorParameter S C z) m
          (fun p => heightPairField S u p - u.2 * S.chiLeft p.1))
        (canonicalOpen S K m)) ∧
      ReferenceGraph D γ M₀ M₁ (v, μ) (n07aReferenceCompatibleSource D K v μ, 0) := by
  have hη := (hS.1 (3 / 4 : ℝ)).2.2.2.1 u.1
  have hηs : ContDiff ℝ ∞ (heightPairField S u) :=
    (heightMember_contDiff_and_flatJets hT (by norm_num : 0 < (3 / 4 : ℝ)) hη).1.add
      (contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst))
  have hηπ : Function.Periodic (heightPairField S u) (0, Real.pi) := by
    intro p
    simp only [heightPairField, hη.2.2.1 p, Prod.fst_add, add_zero]
  have hηe : ∀ r θ, heightPairField S u (r, -θ) = heightPairField S u (r, θ) := by
    intro r θ
    simp only [heightPairField, hη.2.1 r θ]
  obtain ⟨v, hvc, hvπ, hve, hv, hheightCanonical, hzero, hright⟩ :=
    n07a_exists_referenceTransport_C1 hD hT hS h01 h04 href hcanonical
      z hz u.2 hηs hηπ hηe
  let β : ℝ := (γ + (3 / 4 : ℝ)) / 2
  have hβ : 0 < β := by dsimp only [β]; linarith
  have hβhi : β < (3 / 4 : ℝ) := by dsimp only [β]; linarith
  have hγβ : γ < β := by dsimp only [β]; linarith
  obtain ⟨A₀, A₁, B, hA₀, hA₁, hB, hrem, hsource, hjets⟩ :=
    n07a_referenceCandidate_physical_bounds hD hT hS h01 h04 href hcur hRatio z hz u hvc hv hβ hβhi
  have hrowv : referenceRow D v = 0 :=
    (n07a_referenceTransport_row_of_pieces hD.choose_spec.1.2.1.le h01 h04
      (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) u.2 hηπ hvπ hv).trans hrow
  refine ⟨v, hvc, hv, hheightCanonical, ?_⟩
  apply n07a_referenceGraph_of_piecewise_material_bounds hD hT h04 hborder hS.2.2.1
    hvc (n07a_referenceTransport_piece_smooth hS h01 h04 z hz u hv)
    hvπ hve hzero hright hβ hγβ 0 0 hA₀ hA₁ hB
  · simpa only [Real.rpow_zero, mul_one] using hrem
  · simpa only [Real.rpow_zero, mul_one] using hsource
  · exact hjets
  · exact hrowv

end ContinuousFlexibility.Analysis
