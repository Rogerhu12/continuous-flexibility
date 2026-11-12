import ContinuousFlexibility.Analysis.N07aCurrentAngularPatch
import ContinuousFlexibility.Analysis.N07aCurrentCutRegularity
import ContinuousFlexibility.Analysis.N07aAngularPhysicalRepresentative
import ContinuousFlexibility.Analysis.N07aCanonicalSmoothJets

/-!
# Actual canonical weak jets give physical angular jets across all cuts

The smooth decoder is used only on the open pieces. Its true classical
jets are the original canonical weak L² jets. Actual coordinate pullback
and locally finite angular patching then recover the original physical
height remainder on every compact inner strip, including intervals that
cross roots or artificial cuts.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K J : CanonicalData S}
  {base loss n : ℕ} {ε : ℝ}

theorem n07aCanonicalSmoothDecode_memLp (m : ℕ) (hm : K.left m < K.right m)
    (u : n07aCanonicalSmoothSpace S K m) (a b : ℕ) :
    MemLp (mixedDerivative a b (n07aCanonicalSmoothDecode hm u)) 2
      (canonicalMeasure S K m) := by
  obtain ⟨v, hv⟩ := u.property a a le_rfl b
  exact (memLp_congr_ae (n07aCanonicalSmoothDecode_mixed_ae hm a b u v hv)).mpr (Lp.memLp v)

/-- This is the same physical representative supplied by the original
weak relation, after subtracting its explicit left scalar column. -/
theorem n07a_representation_local_angularRegular
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hborder : RadialTrueBorder D)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (liftSectorParameter S C z) U F η f)
    (hU : ∀ m n, N07aCanonicalNormalRegular S K m (U.1 m) n)
    (hreference : N07aReferenceGraphRepresentation D S C K U)
    (f₀ : S.Source)
    (hnormal : N07aActualNormalEquation D S C L K z U f₀
      (fun m => n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
        ⟨U.1 m, hU m⟩))
    (hinner : Icc (J.left n) (J.right n) ⊆ Ioo D.a D.b) :
    ∃ u : CanonicalL2 S J n, N07aCanonicalNormalRegular S J n u 0 ∧
      (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n]
        fun p => η p - U.2.1 * S.chiLeft p.1 := by
  classical
  let u (m : ℕ) : n07aCanonicalSmoothSpace S K m := ⟨U.1 m, hU m⟩
  have hm (m : ℕ) : K.left m < K.right m := (h04.1.referenceBounds m).2.1
  let v (m : ℕ) : PolarPoint → ℝ := n07aCanonicalSmoothDecode (hm m) (u m)
  have hv (m : ℕ) := n07aCanonicalSmoothRepresentative_properties (hm m) (u m)
  let Jc (m : ℕ) : ClosedJetTower (K.left m) (K.right m) (v m) :=
    n07aCanonicalClosedJets (hm m) (u m)
  let w (m : ℕ) : PolarPoint → ℝ :=
    n07aClosedPhysicalHeight K (liftSectorParameter S C z) m (Jc m)
  have hweq (m : ℕ) := n07aClosedPhysicalHeight_eqOn h04 hz' hs m (Jc m)
  have hwclosed (m : ℕ) := n07aClosedPhysicalHeight_contDiffOn h04 hz' hs m (Jc m)
  apply n07a_current_physical_local_angular_regular hD hT h04 href h01.2.2.2.1
    hz' hs hinner w
  · intro m
    exact (hwclosed m).mono subset_closure
  · intro m
    exact (hwclosed m).continuousOn
  · intro m p hp
    have hp' : p + (0, Real.pi) ∈ physicalPieceOpen S K (liftSectorParameter S C z) m :=
      ((h04.1.domains _ hz' hs m).2.2.2.1 p).mpr hp
    exact (hweq m hp').trans
      ((n07aPhysicalHeightRepresentative_periodic_on h04 hz' hs m (hv m).2.1 p hp).trans
        (hweq m hp).symm)
  · intro m k
    have he : mixedDerivative 0 k (w m) =ᵐ[
        n07aPhysicalMeasure S K (liftSectorParameter S C z) m]
        mixedDerivative 0 k (n07aPhysicalHeightRepresentative K
          (liftSectorParameter S C z) m (v m)) := by
      filter_upwards [n07aPhysicalMeasure_ae h04 hz' hs m] with p hp
      exact n07a_mixedDerivative_eqOn (h04.1.domains _ hz' hs m).1 (hweq m) 0 k hp
    exact (memLp_congr_ae he).mpr
      (n07aPhysicalHeightRepresentative_angular_memLp h04 href hcur z hz hz' hs m
        (hv m).1 (n07aCanonicalSmoothDecode_memLp m (hm m) (u m)) k)
  · intro m
    filter_upwards [n07aPhysicalHeightRepresentative_ae h04 hz' hs hrep m (hv m).2.2.1.symm,
      n07aPhysicalMeasure_ae h04 hz' hs m] with p hp hpm
    exact (hweq m hpm).trans hp
  · intro k θ
    exact n07a_actualCanonical_cut_smooth_gluing hD hT hS h01 h04 hcanonical hborder
      z hz' hs hreference (fun m => (hv m).1) (fun m => (hv m).2.1)
      (fun m => (hv m).2.2.1.symm) Jc f₀ hnormal k θ
      (Classical.choice (n07a_tubularCutCoordinates_exists h04 hz' hs k θ))

end ContinuousFlexibility.Analysis
