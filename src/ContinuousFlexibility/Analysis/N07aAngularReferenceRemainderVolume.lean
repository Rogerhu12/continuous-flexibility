import ContinuousFlexibility.Analysis.N07aAngularReferenceLowJets
import ContinuousFlexibility.Analysis.N07aAngularReferenceDifferentialJets
import ContinuousFlexibility.Analysis.N07aAngularReferenceSourceEnvelopes
import ContinuousFlexibility.Analysis.N07aAngularFixedVolume

/-!
# The reference remainder source is in the actual canonical source graph

For an arbitrary physical height pair, the reference C¹ realization has
the same actual remainder on each open piece. Its genuine differential
source keeps all sampled material powers and every angular jet.
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
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

def n07aReferenceRemainderDifferential (D : ReferenceData) (S : PhysicalSpacesData)
    (v : PolarPoint → ℝ) (aL : ℝ) : PolarPoint → ℝ :=
  n07aReferenceDifferential D (fun p => v p - aL * S.chiLeft p.1)

theorem n07a_referenceRemainderSource_volume
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hV : IsVolumeModel T S K V)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) {v : PolarPoint → ℝ}
    (hvp : Function.Periodic v (0, Real.pi)) (hve : ∀ r θ, v (r, -θ) = v (r, θ))
    (hv : ∀ m, EqOn v (n07aReferencePieceHeight C K (liftSectorParameter S C z)
      (K.inverseChart (liftSectorParameter S C z)) u.2 (heightPairField S u) m)
      (referencePhysicalPieceOpen S K m)) (t s : ℕ) :
    ∃ Fts : V.level (3 / 4 : ℝ) (t : ℝ) s,
      ∀ m, (V.forget (3 / 4 : ℝ) (t : ℝ) s Fts m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          canonicalSource S K (C.referenceState, 0) m
            (n07aReferenceRemainderDifferential D S v u.2) := by
  let r₀ : PolarPoint → ℝ := fun p => v p - u.2 * S.chiLeft p.1
  have hvsm := n07a_referenceTransport_piece_smooth hS h01 h04 z hz u hv
  have hχ : ContDiff ℝ ∞ (fun p : PolarPoint => u.2 * S.chiLeft p.1) :=
    contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)
  have hrs (m : ℕ) : ContDiffOn ℝ ∞ r₀ (referencePhysicalPieceOpen S K m) :=
    (hvsm m).sub hχ.contDiffOn
  have hrp : Function.Periodic r₀ (0, Real.pi) := by
    intro p
    simp only [r₀, hvp p, Prod.fst_add, add_zero]
  have hre : ∀ r θ, r₀ (r, -θ) = r₀ (r, θ) := by
    intro r θ
    simp only [r₀, hve r θ]
  have hgsm (m : ℕ) : ContDiffOn ℝ ∞ (n07aReferenceRemainderDifferential D S v u.2)
      (referencePhysicalPieceOpen S K m) :=
    n07a_referenceDifferential_contDiffOn hD.choose_spec.1 (isOpen_Ioo.prod isOpen_univ)
      (fun p hp => ⟨(h04.1.referenceBounds m).2.2 hp.1, mem_univ _⟩) (hrs m)
  have hgperiod : Function.Periodic (n07aReferenceRemainderDifferential D S v u.2)
      (0, Real.pi) := n07aReferenceDifferential_periodic D hrp
  have hgeven : ∀ r θ, n07aReferenceRemainderDifferential D S v u.2 (r, -θ) =
      n07aReferenceRemainderDifferential D S v u.2 (r, θ) :=
    n07aReferenceDifferential_even D hre
  have henv (c : ℕ) : N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹) (fun _ => r₀) := by
    apply (n07a_referenceRemainder_fixedJetEnvelope hD hT hS h01 h04 href hcur hRatio z hz u.1 c).congr
      (fun _ => isOpen_Ioo.prod isOpen_univ)
    intro m p hp
    have he := congrFun (n07aReferencePieceHeight_eq_remainder C K
      (liftSectorParameter S C z) u m) p
    exact congrArg (fun a : ℝ => a - u.2 * S.chiLeft p.1) ((hv m hp).trans he)
      |>.trans (add_sub_cancel_right _ _)
  have hw (c m : ℕ) : 0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
      (T.M (T.sample (K.cell m)) ^ c)⁻¹ := by
    have hp := hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_nonneg (Real.rpow_nonneg hp.2.1.le _)
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hp.2.2.2) c))
  have hcan (c : ℕ) : N07aAngularFixedJetEnvelope T K (canonicalOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      (fun m => canonicalSource S K (C.referenceState, 0) m
        (n07aReferenceRemainderDifferential D S v u.2)) :=
    n07a_referenceSource_fixedJetEnvelope hD hT h01 h04 href hcur (hw c) hgsm
      (n07a_referenceDifferential_fixedJetEnvelope hD hT
        (fun m => (h04.1.referenceBounds m).2.2) (hw c) hrs (henv c))
  apply n07a_fixedJetEnvelope_volume hD hT h04 href hV
    (n07a_referenceSource_piece_contDiffOn h01 h04 href hgsm) ?_ ?_ hcan t s
  · intro m
    simpa only [n07a_lift_zero_parameter] using
      n07a_canonicalSource_periodic_on h01.2.2.1 h04 hcur
        0 (n07a_zero_parameter_mem h01) hgperiod m
  · exact n07a_canonicalSource_even_on h04 (n07a_reference_mem_stateNeighborhood h01)
      h01.2.2.1.stateSector hgeven

end ContinuousFlexibility.Analysis
