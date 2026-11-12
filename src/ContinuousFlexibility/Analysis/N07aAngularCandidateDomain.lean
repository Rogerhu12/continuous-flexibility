import ContinuousFlexibility.Analysis.N07aAngularReferenceCandidate
import ContinuousFlexibility.Analysis.N07aAngularReferenceSourceVolume
import ContinuousFlexibility.Analysis.N07aAngularCandidateCoordinates
import ContinuousFlexibility.Analysis.N07aAngularVolumeSequence
import ContinuousFlexibility.Analysis.N07aAngularMaterialLowering

/-!
# Every normalized physical height pair enters the actual N05 graph

The reference witness is the C¹ field transported through the prescribed
current and reference charts. Its genuine compatible differential source
lies in the original base source level. The natural physical graph and
the original graph equivalence of N05 therefore give domain membership.
The candidate need not satisfy a perturbed differential equation here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {B : CanonicalDomainData S K V b} {ε : ℝ}

theorem n07a_currentHeightPair_enters_referenceDomain
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hborder : RadialTrueBorder D)
    (hrad : CanonicalGeometry.ReferenceRadial S C K)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (htrans : CanonicalGeometry.TransmissionGeometry D S C K base ε)
    (h05 : N05Properties D T S C K V b B)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) (μ : ℝ)
    (hrow : referenceRow D (heightPairField S u) = 0) :
    ∃ d : B.Space,
      d.val.1.2.1 = u.2 ∧ d.val.1.2.2.1 = μ ∧ d.val.1.2.2.2 = 0 ∧
      ∀ m, (d.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K (liftSectorParameter S C z) m
          ((S.height (3 / 4 : ℝ)).decode u.1) := by
  have hV := h05.2.1
  have reference := n07a_exists_referenceGraph_of_current_heightPair
    hD hT hS h01 h04 hborder hrad href hcur htrans z hz u μ
    B.weakExponent B.sourceMaterial B.outputMaterial h05.2.2.1 h05.2.2.2.1 hrow
  let v : PolarPoint → ℝ := reference.choose
  have hvc : ContDiffOn ℝ 1 v (annularOpen D) := reference.choose_spec.1
  have hv := reference.choose_spec.2.1
  have hcanonical := reference.choose_spec.2.2.1
  have hgraph : ReferenceGraph D B.weakExponent B.sourceMaterial B.outputMaterial
      (v, μ) (n07aReferenceCompatibleSource D K v μ, 0) := reference.choose_spec.2.2.2
  have hvp : Function.Periodic v (0, Real.pi) := hgraph.1.choose_spec.2.2.1
  have hve : ∀ r θ, v (r, -θ) = v (r, θ) := hgraph.1.choose_spec.2.2.2
  let realizes (s : ℕ) (f : ℕ → PolarPoint → ℝ) (t : ℝ) : Prop :=
    ∃ A : V.level (3 / 4 : ℝ) t s,
      ∀ m, (V.forget (3 / 4 : ℝ) t s A m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] f m
  have hcast : ((0 : ℕ) : ℝ) = 0 := by norm_num
  have sourceNat : realizes b
      (fun m => canonicalSource S K (C.referenceState, 0) m
        (n07aReferenceCompatibleSource D K v μ)) ((0 : ℕ) : ℝ) :=
    n07a_referenceCompatibleSource_volume
      hD hT hS h01 h02 h03 h04 href hcur hV z hz u μ hvp hve hv 0 b
  have source : realizes b
      (fun m => canonicalSource S K (C.referenceState, 0) m
        (n07aReferenceCompatibleSource D K v μ)) 0 :=
    Eq.mp (congrArg (realizes b (fun m => canonicalSource S K
      (C.referenceState, 0) m (n07aReferenceCompatibleSource D K v μ))) hcast) sourceNat
  let F : V.level (3 / 4 : ℝ) 0 b := source.choose
  have hF := source.choose_spec
  have remainderNat : realizes 0
      (fun m => canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u.1)) ((0 : ℕ) : ℝ) :=
    n07a_currentHeight_volume hD hT hS h01 h04 href hcur hV z hz u.1 0 0
  have remainder : realizes 0
      (fun m => canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u.1)) 0 :=
    Eq.mp (congrArg (realizes 0 (fun m => canonicalHeight S K
      (liftSectorParameter S C z) m ((S.height (3 / 4 : ℝ)).decode u.1))) hcast) remainderNat
  let W : V.level (3 / 4 : ℝ) 0 0 := remainder.choose
  have hW := remainder.choose_spec
  let U : CanonicalUnknown S K :=
    (n07aPositiveHeightVolumeSequence hD hT hV (by norm_num : (0 : ℝ) < 3 / 4) W,
      (u.2, μ, 0))
  have hU (m : ℕ) : (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode u.1) := by
    have he : U.1 m = V.forget (3 / 4 : ℝ) 0 0 W m :=
      n07aPositiveHeightVolumeSequence_apply hD hT hV
        (by norm_num : (0 : ℝ) < 3 / 4) W m
    have hefun := congrArg (fun q : CanonicalL2 S K m => (q : PolarPoint → ℝ)) he
    have hae : (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        (V.forget (3 / 4 : ℝ) 0 0 W m : PolarPoint → ℝ) :=
      Eventually.of_forall (fun p => congrFun hefun p)
    exact hae.trans (hW m)
  have hmaterial : VolumeMember S K V (3 / 4 : ℝ) (-B.lossMaterial) 0
      (fun m => U.1 m) := by
    apply n07a_volumeMember_lower_material hD hT hV
      (neg_nonpos.mpr h05.2.2.2.2.1)
    exact ⟨W, funext fun m =>
      (n07aPositiveHeightVolumeSequence_apply hD hT hV
        (by norm_num : (0 : ℝ) < 3 / 4) W m).symm⟩
  have hrep : HasCanonicalRepresentation D S C K (C.referenceState, 0) U
      (V.forget (3 / 4 : ℝ) 0 b F) v (n07aReferenceCompatibleSource D K v μ) := by
    refine ⟨fun m => ?_, hF⟩
    have hrem : (fun p => heightPairField S u p - u.2 * S.chiLeft p.1) =
        (S.height (3 / 4 : ℝ)).decode u.1 := by
      funext p
      exact add_sub_cancel_right _ _
    have hremCanonical :
        canonicalHeight S K (liftSectorParameter S C z) m
          (fun p => heightPairField S u p - u.2 * S.chiLeft p.1) =
        canonicalHeight S K (liftSectorParameter S C z) m
          ((S.height (3 / 4 : ℝ)).decode u.1) :=
      congrArg (canonicalHeight S K (liftSectorParameter S C z) m) hrem
    have hcan : canonicalHeight S K (C.referenceState, 0) m
        (fun p => v p - u.2 * S.chiLeft p.1) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K (liftSectorParameter S C z) m
          ((S.height (3 / 4 : ℝ)).decode u.1) :=
      (n07a_canonicalOpen_ae (S := S) (K := K) (m := m)).mono
        (fun p hp => (hcanonical m hp).trans (congrFun hremCanonical p))
    exact (hU m).trans hcan.symm
  have hrel : ReferenceCanonicalRelation D T S C K V B.weakExponent
      B.sourceMaterial B.outputMaterial B.lossMaterial U
        (V.forget (3 / 4 : ℝ) 0 b F) := by
    refine ⟨hmaterial, v, n07aReferenceCompatibleSource D K v μ, hrep, ?_⟩
    simpa only [U, zero_mul, sub_zero] using hgraph
  let d : B.Space := ⟨(U, F), (h05.2.2.2.2.2.2.1 (U, F)).mpr hrel⟩
  exact ⟨d, rfl, rfl, rfl, hU⟩

end ContinuousFlexibility.Analysis
