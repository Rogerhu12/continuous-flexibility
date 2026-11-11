import ContinuousFlexibility.Analysis.N07aAngularPhysicalSolution
import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
import ContinuousFlexibility.Scalar.WeightedDecodeLift
import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# The original physical remainder in the actual height decoder

Only the height remainder is extended by zero. On the physical core its
decoded height pair is the same smooth solution and has exactly the same
normalization and differential equation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

def n07aPhysicalRemainder (D : ReferenceData) (S : PhysicalSpacesData)
    (a : ℝ) (v : PolarPoint → ℝ) : PolarPoint → ℝ :=
  (annularOpen D).indicator (fun p => v p - a * S.chiLeft p.1)

theorem n07aPhysicalRemainder_apply {a : ℝ} {v : PolarPoint → ℝ}
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    n07aPhysicalRemainder D S a v p = v p - a * S.chiLeft p.1 :=
  Set.indicator_of_mem hp _

theorem n07aPhysicalRemainder_zero {a : ℝ} {v : PolarPoint → ℝ}
    {p : PolarPoint} (hp : p ∉ annularOpen D) :
    n07aPhysicalRemainder D S a v p = 0 := Set.indicator_of_notMem hp _

theorem n07aPhysicalRemainder_smooth (hS : IsPhysicalSpaces D T S)
    {a : ℝ} {v : PolarPoint → ℝ} (hv : ContDiffOn ℝ ∞ v (annularOpen D)) :
    ContDiffOn ℝ ∞ (n07aPhysicalRemainder D S a v) (annularOpen D) :=
  (hv.sub (contDiffOn_const.mul
    (hS.2.2.1.1.comp contDiff_fst).contDiffOn)).congr
      (fun _ hp => n07aPhysicalRemainder_apply hp)

theorem n07aPhysicalRemainder_periodic {a : ℝ} {v : PolarPoint → ℝ}
    (hv : Function.Periodic v (0, Real.pi)) :
    Function.Periodic (n07aPhysicalRemainder D S a v) (0, Real.pi) := by
  intro p
  have hpiff : p + (0, Real.pi) ∈ annularOpen D ↔ p ∈ annularOpen D := by
    simp only [annularOpen, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, and_true,
      Prod.fst_add, add_zero]
  by_cases hp : p ∈ annularOpen D
  · rw [n07aPhysicalRemainder_apply (hpiff.mpr hp), n07aPhysicalRemainder_apply hp,
      hv p, Prod.fst_add, add_zero]
  · rw [n07aPhysicalRemainder_zero (fun h => hp (hpiff.mp h)),
      n07aPhysicalRemainder_zero hp]

theorem n07aPhysicalRemainder_even {a : ℝ} {v : PolarPoint → ℝ}
    (hv : ∀ r θ, v (r, -θ) = v (r, θ)) :
    ∀ r θ, n07aPhysicalRemainder D S a v (r, -θ) =
      n07aPhysicalRemainder D S a v (r, θ) := by
  intro r θ
  by_cases hr : r ∈ Ioo D.a D.b
  · rw [n07aPhysicalRemainder_apply ⟨hr, mem_univ _⟩,
      n07aPhysicalRemainder_apply ⟨hr, mem_univ _⟩, hv r θ]
  · rw [n07aPhysicalRemainder_zero (fun h => hr h.1),
      n07aPhysicalRemainder_zero (fun h => hr h.1)]

/-- The actual canonical smooth representative reconstructs the original
physical remainder pointwise on every actual open piece. -/
theorem n07aPhysicalRemainder_eqOn
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {v f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F v f)
    (hU : ∀ m n, N07aCanonicalNormalRegular S K m (U.1 m) n)
    (hv : ContDiffOn ℝ ∞ v (annularOpen D))
    (hvp : Function.Periodic v (0, Real.pi)) (m : ℕ) :
    EqOn (n07aPhysicalRemainder D S U.2.1 v)
      (n07aPhysicalHeightRepresentative K z m
        (n07aCanonicalSmoothDecode (h04.2.2.2.1 m).2.1 ⟨U.1 m, hU m⟩))
      (physicalPieceOpen S K m) := by
  let u : n07aCanonicalSmoothSpace S K m := ⟨U.1 m, hU m⟩
  have hw := n07aCanonicalSmoothRepresentative_properties (h04.2.2.2.1 m).2.1 u
  have hsub : physicalPieceOpen S K m ⊆ annularOpen D :=
    fun _ hp => ⟨(h04.2.2.2.1 m).2.2 hp.1, mem_univ _⟩
  have he := n07a_canonical_periodicOn_eqOn_of_ae_eq
    (S := S) (K := n07aPhysicalIntervalData K) (m := m)
    (n07aPhysicalHeightRepresentative_contDiffOn h04 hz hs m hw.1).continuousOn
    ((hv.mono hsub).sub (contDiffOn_const.mul
      (hS.2.2.1.1.comp contDiff_fst).contDiffOn)).continuousOn
    (n07aPhysicalHeightRepresentative_periodic_on h04 hz hs m hw.2.1)
    (fun p _ => by simp only [Function.comp_apply, hvp p, Prod.fst_add, add_zero])
    (n07aPhysicalHeightRepresentative_ae h04 hz hs hrep m hw.2.2.1.symm)
  intro p hp
  exact (n07aPhysicalRemainder_apply (hsub hp)).trans (he hp).symm

theorem n07aPhysicalRemainder_heightMember
    (hS : IsPhysicalSpaces D T S) {a γ : ℝ} {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v (annularOpen D))
    (hvp : Function.Periodic v (0, Real.pi)) (hve : ∀ r θ, v (r, -θ) = v (r, θ))
    (hLp : ∀ i j k, MemLp
      (weightedPhysicalJet T γ i j k (n07aPhysicalRemainder D S a v))
      2 materialCylinderMeasure) :
    HeightMember D T γ (n07aPhysicalRemainder D S a v) :=
  ⟨n07aPhysicalRemainder_smooth hS hv, n07aPhysicalRemainder_even hve,
    n07aPhysicalRemainder_periodic hvp, fun _ hp => n07aPhysicalRemainder_zero hp, hLp⟩

def n07aPhysicalHeightPair (hS : IsPhysicalSpaces D T S) (a : ℝ)
    (v : PolarPoint → ℝ)
    (hmem : HeightMember D T (3 / 4 : ℝ) (n07aPhysicalRemainder D S a v)) :
    HeightPair S :=
  (SobolevModelData.liftHeight (hS.1 (3 / 4 : ℝ)) _ hmem, a)

theorem n07aPhysicalHeightPair_field (hS : IsPhysicalSpaces D T S) (a : ℝ)
    (v : PolarPoint → ℝ)
    (hmem : HeightMember D T (3 / 4 : ℝ) (n07aPhysicalRemainder D S a v)) :
    EqOn (heightPairField S (n07aPhysicalHeightPair hS a v hmem)) v (annularOpen D) := by
  intro p hp
  simp only [heightPairField, n07aPhysicalHeightPair,
    SobolevModelData.decode_liftHeight, n07aPhysicalRemainder_apply hp]
  ring

theorem n07aPhysicalHeightPair_grading (hS : IsPhysicalSpaces D T S) (a : ℝ)
    (v : PolarPoint → ℝ)
    (hmem : HeightMember D T (3 / 4 : ℝ) (n07aPhysicalRemainder D S a v)) (s : ℕ) :
    heightPairGrading S s (n07aPhysicalHeightPair hS a v hmem) =
      physicalNorm T (3 / 4 : ℝ) s (n07aPhysicalRemainder D S a v) + |a| := by
  simp only [heightPairGrading, pairGrading_apply, n07aPhysicalHeightPair,
    sobolevGrading_eq_physicalNorm (hS.1 (3 / 4 : ℝ)),
    SobolevModelData.decode_liftHeight, realGrading, coe_normSeminorm, Real.norm_eq_abs]

end ContinuousFlexibility.Analysis
