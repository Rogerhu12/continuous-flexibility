import ContinuousFlexibility.Analysis.N07aActualCanonicalSolutionData
import ContinuousFlexibility.Analysis.N07aPhysicalSolutionFamily
import ContinuousFlexibility.Analysis.N07aPhysicalReconstructionJets
import ContinuousFlexibility.Analysis.N07aPhysicalCandidateBounds
import ContinuousFlexibility.Analysis.N07aNuSource
import ContinuousFlexibility.Analysis.N07aParameterNeighborhood
import ContinuousFlexibility.Analysis.SolveResidualSpaces

/-!
# The same canonical inverse gives the actual physical candidate family

The canonical representative, the true chart and the original height
factor are used in sequence. One fixed low-order neighborhood controls
the complete reconstruction and the genuine distinguished Source column.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem n07a_candidate_with_exists {α : Type*} {Condition : α → Prop} {P : Prop}
    (h : ∃ a, Condition a) (hP : ∀ a, Condition a → P) : P := by
  obtain ⟨a, ha⟩ := h
  exact hP a ha

private theorem n07a_candidate_with_orders {Condition : ℕ → ℕ → Prop} {P : Prop}
    (h : ∃ low loss, Condition low loss)
    (hP : ∀ low loss, Condition low loss → P) : P := by
  obtain ⟨low, loss, hbound⟩ := h
  exact hP low loss hbound

private theorem n07a_candidate_with_neighborhood
    {base : ℕ} {ε : ℝ} {Condition : ℕ → ℝ → Prop} {P : Prop}
    (h : ∃ b, base ≤ b ∧ ∃ η, 0 < η ∧ η ≤ ε ∧ Condition b η)
    (hP : ∀ b, base ≤ b → ∀ η, 0 < η → η ≤ ε → Condition b η → P) : P := by
  obtain ⟨b, hb, η, hη, hηε, hbound⟩ := h
  exact hP b hb η hη hηε hbound

private theorem n07a_candidate_solution_prefix {A B C D E F : Prop}
    (h : A ∧ B ∧ C ∧ D ∧ E ∧ F) : A ∧ B ∧ C ∧ D ∧ E :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

private theorem n07a_candidate_scalar_pair_bound
    {S : PhysicalSpacesData} {K : CanonicalData S} (U : CanonicalUnknown S K)
    (A q : ℝ) (h : ∀ i : Fin 3, |n07aUnknownScalar U i| ≤ A * q) :
    |U.2.1| + |U.2.2.1| ≤ (2 * A) * q := by
  have h0 : |U.2.1| ≤ A * q := by
    simpa only [n07aUnknownScalar, Matrix.cons_val_zero] using h 0
  have h1 : |U.2.2.1| ≤ A * q := by
    simpa only [n07aUnknownScalar, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.tail_cons] using h 1
  exact (add_le_add h0 h1).trans_eq (by ring)

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
  {base geometryLoss : ℕ} {ε : ℝ}

theorem n07a_exists_boundedPhysicalCandidate
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base geometryLoss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base geometryLoss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hFirst : N07aActualForwardFirstBound T S C K base ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (data : N07aActualCanonicalSolutionData D T S C L K V b B P base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ u : CanonicalGeometry.Parameter S → S.Source → HeightPair S × ℝ,
        (∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ f,
          N07aScalarSolution D S C L (liftSectorParameter S C z) f (u z f)) ∧
        ∃ d low : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
          ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ f,
            n07aOutputGrading S s (u z f) ≤ A *
              (S.sourceGrading (s + d) f +
                (1 + CanonicalGeometry.parameterGrading S (s + d) z) * S.sourceGrading low f) := by
  let Ω := sectorNeighborhood S base ε ε
  let p := CanonicalGeometry.parameterGrading S
  let wgt : ℕ → ℕ → ℝ := fun c m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
    (T.M (T.sample (K.cell m)) ^ c)⁻¹
  have hwgt (c m : ℕ) : 0 ≤ wgt c m := by
    have hm := hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_nonneg (Real.rpow_nonneg hm.2.1.le _)
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.2.2.2) c))
  have hws (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) (m : ℕ) :
      ContDiffOn ℝ ∞ (data.w z f m) (canonicalOpen S K m) := by
    exact data.smooth z hz f m
  have hreference (z : CanonicalGeometry.Parameter S) (_hz : z ∈ Ω) (f : S.Source) :
      N07aReferenceGraphRepresentation D S C K (data.U z f) :=
    ⟨B.weakExponent, B.sourceMaterial, B.outputMaterial, data.referenceGraph h05 z f⟩
  have hnormal (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :
      N07aActualNormalEquation D S C L K z (data.U z f) f (data.w z f) := by
    intro m
    exact data.equation z hz f m
  refine n07a_candidate_with_exists
    (n07a_exists_actualPhysicalSolutionFamily hD hT hS h01 h03 h04
      href hcur hcanonical h01.1.2.2.2.1 Ω Subset.rfl data.U data.F data.relation
      data.regular hreference data.even data.sourceAE data.w data.decode hnormal) ?_
  intro v hv
  let r := fun z f => n07aPhysicalRemainder D S (data.U z f).2.1 (v z f)
  refine n07a_candidate_with_orders
    (n07a_physicalReconstruction_sampleJets hD hT hS h01.2.2.1
      h04 href hcur hFirst S.sourceGrading (n07aSourceGrading_monotone S)
      (solve_source_hasSmoothing hS) Ω Subset.rfl wgt hwgt data.w r data.low data.loss
      data.jets hws (fun z hz f m => (hv z hz f).2.2.2.2.2 m)) ?_
  intro lowr dr hr
  refine n07a_candidate_with_neighborhood (n07a_exists_nuSource hS hT h01) ?_
  intro baseN hbaseN εN hεN hεNle nuNeighborhood
  refine n07a_candidate_with_exists nuNeighborhood ?_
  intro N hNall
  have hN := hNall.2
  refine n07a_candidate_with_neighborhood
    (n07a_lowParameter_neighborhood (S := S) (base := baseN) hεN lowr) ?_
  intro base' hbase' ε' hε' hε'le smallNeighborhood
  have hsubN := smallNeighborhood.1
  have hsmall := smallNeighborhood.2
  let Ω' := sectorNeighborhood S base' ε' ε'
  have hsub : Ω' ⊆ Ω :=
    fun z hz => n07a_sectorNeighborhood_mono (S := S) hbaseN hεNle (hsubN hz)
  have hsample : N07aStateSampleLinearJetBounds T K p S.sourceGrading Ω'
      (fun z m => physicalPieceOpen S K (liftSectorParameter S C z) m) wgt lowr dr (fun z f _ => r z f) :=
    hr.restrict (fun z (hz : z ∈ Ω') => ⟨hsub hz, hsmall z hz⟩)
  have hscalars (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω') (f : S.Source) :
      |(data.U z f).2.1| + |(data.U z f).2.2.1| ≤
        (2 * data.Cα) * S.sourceGrading data.low f :=
    n07a_candidate_scalar_pair_bound (data.U z f) data.Cα (S.sourceGrading data.low f)
      (data.scalars z (hsub hz) f)
  refine n07a_candidate_with_exists (n07a_exists_actualHeightCandidateFamily
    hD hT hS h01 h02 h03 h04 href hRatio Ω' hsub data.U v
    (fun z hz f => n07a_candidate_solution_prefix (hv z (hsub hz) f))
    N (fun z hz => hN z (hsubN hz)) lowr dr data.low (2 * data.Cα)
    (mul_nonneg (by norm_num) data.Cα_nonneg) hscalars hsample) ?_
  intro η hη
  exact ⟨base', hbaseN.trans hbase', ε', hε', hε'le.trans hεNle,
    fun z f => (η z f, (data.U z f).2.2.1), hη.1, hη.2⟩

end ContinuousFlexibility.Analysis
