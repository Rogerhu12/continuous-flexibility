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
  have family := n07a_exists_actualPhysicalSolutionFamily hD hT hS h01 h03 h04
    href hcur Ω Subset.rfl data.U data.F data.relation data.regular data.even
    data.sourceAE data.w data.decode
  let v : CanonicalGeometry.Parameter S → S.Source → PolarPoint → ℝ := family.choose
  have hv := family.choose_spec
  let r := fun z f => n07aPhysicalRemainder D S (data.U z f).2.1 (v z f)
  have reconstruction := n07a_physicalReconstruction_sampleJets hD hT hS h01.2.2.1
    h04 href hcur S.sourceGrading (n07aSourceGrading_monotone S) (solve_source_hasSmoothing hS)
    Ω Subset.rfl wgt hwgt data.w r data.low data.loss data.jets hws
    (fun z hz f m => (hv z hz f).2.2.2.2.2 m)
  let lowr : ℕ := reconstruction.choose
  let dr : ℕ := reconstruction.choose_spec.choose
  have hr := reconstruction.choose_spec.choose_spec
  have nuFamily := n07a_exists_nuSource hS hT h01
  let baseN : ℕ := nuFamily.choose
  have hbaseN : base ≤ baseN := nuFamily.choose_spec.1
  let εN : ℝ := nuFamily.choose_spec.2.choose
  have nuNeighborhood := nuFamily.choose_spec.2.choose_spec
  have hεN : 0 < εN := nuNeighborhood.1
  have hεNle : εN ≤ ε := nuNeighborhood.2.1
  let N : CanonicalGeometry.Parameter S → S.Source := nuNeighborhood.2.2.choose
  have hN := nuNeighborhood.2.2.choose_spec.2
  have shrink := n07a_lowParameter_neighborhood (S := S) (base := baseN) hεN lowr
  let base' : ℕ := shrink.choose
  have hbase' : baseN ≤ base' := shrink.choose_spec.1
  let ε' : ℝ := shrink.choose_spec.2.choose
  have smallNeighborhood := shrink.choose_spec.2.choose_spec
  have hε' : 0 < ε' := smallNeighborhood.1
  have hε'le : ε' ≤ εN := smallNeighborhood.2.1
  have hsubN := smallNeighborhood.2.2.1
  have hsmall := smallNeighborhood.2.2.2
  let Ω' := sectorNeighborhood S base' ε' ε'
  have hsub : Ω' ⊆ Ω :=
    fun z hz => n07a_sectorNeighborhood_mono (S := S) hbaseN hεNle (hsubN hz)
  have hsample : N07aSampleLinearJetBounds T K p S.sourceGrading Ω'
      (physicalPieceOpen S K) wgt lowr dr (fun z f _ => r z f) :=
    hr.restrict (fun z (hz : z ∈ Ω') => ⟨hsub hz, hsmall z hz⟩)
  have hscalars (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω') (f : S.Source) :
      |(data.U z f).2.1| + |(data.U z f).2.2.1| ≤
        (2 * data.Cα) * S.sourceGrading data.low f := by
    have h0 : |(data.U z f).2.1| ≤ data.Cα * S.sourceGrading data.low f := by
      simpa only [N07aActualCanonicalSolutionData.U, n07aUnknownScalar, Matrix.cons_val_zero] using data.scalars z (hsub hz) f 0
    have h1 : |(data.U z f).2.2.1| ≤ data.Cα * S.sourceGrading data.low f := by
      simpa only [N07aActualCanonicalSolutionData.U, n07aUnknownScalar, Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
        using data.scalars z (hsub hz) f 1
    exact (add_le_add h0 h1).trans_eq (by ring)
  have candidate := n07a_exists_actualHeightCandidateFamily
    hD hT hS h01 h02 h03 h04 href Ω' hsub data.U v
    (fun z hz f => ⟨(hv z (hsub hz) f).1, (hv z (hsub hz) f).2.1,
      (hv z (hsub hz) f).2.2.1, (hv z (hsub hz) f).2.2.2.1,
      (hv z (hsub hz) f).2.2.2.2.1⟩)
    N (fun z hz => hN z (hsubN hz)) lowr dr data.low (2 * data.Cα)
    (mul_nonneg (by norm_num) data.Cα_nonneg) hscalars hsample
  let η : CanonicalGeometry.Parameter S → S.Source → HeightPair S := candidate.choose
  have hη := candidate.choose_spec.1
  let d : ℕ := candidate.choose_spec.2.choose
  let low : ℕ := candidate.choose_spec.2.choose_spec.choose
  have hbound := candidate.choose_spec.2.choose_spec.choose_spec
  exact ⟨base', hbaseN.trans hbase', ε', hε', hε'le.trans hεNle,
    fun z f => (η z f, (data.U z f).2.2.1), hη, d, low, hbound⟩

end ContinuousFlexibility.Analysis
