module

public import ContinuousFlexibility.Analysis.N05CanonicalSourceWeakCore
public import ContinuousFlexibility.Analysis.N05CanonicalGraphDensity

/-!
# All weak angular jets of the same actual canonical source lift

The genuine smooth graph core satisfies the physical weak identities.
Its graph-norm density and the continuity of each fixed unsigned source
column preserve those identities. The zero column is finally identified
with the source lift already used by the global inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  {γw γ : ℝ} (hγw : 0 < γw) (hgap : γw < γ) (t M : ℝ)

include h hcoordinates hD hT hγw hgap M in
theorem n05CanonicalJetSource_smooth_core_weak (s : ℕ) (j : Fin (s + 1))
    (v : n05CanonicalClosedSubmodule S K s)
    (hv : v ∈ n05CanonicalSmoothCoreSubmodule S K s) :
    n05_weakReferenceAngularJet D (n05CanonicalJetSource T S C K γ t s 0 v.val)
      (n05CanonicalJetSource T S C K γ t s j v.val) j.val := by
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  obtain ⟨_, _, hb⟩ :=
    n05CanonicalJetSource_reference_bound h hcoordinates hD hT hγw.le hgap t M
  have hLp (k : Fin (s + 1)) (x : CanonicalVolumeJets S K s) :
      MemLp (n05CanonicalJetSource T S C K γ t s k x) 2 (radialPhysicalMeasure D) :=
    r11b_sourceDerivative_memLp hD hγw (hb s k x).1
  change v ∈ Submodule.span ℝ (n05CanonicalSmoothSingleCarrier S K s) at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨m, φ, hφ, he, rfl⟩
      exact n05CanonicalJetSource_smooth_single_weak h hcoordinates hab γ t m s hφ j
  | zero =>
      have hzero (k : Fin (s + 1)) :
          n05CanonicalJetSource T S C K γ t s k (0 : CanonicalVolumeJets S K s)
            =ᵐ[radialPhysicalMeasure D] (fun _ => 0) := by
        simpa only [zero_smul, add_zero, zero_mul] using
          n05CanonicalJetSource_linear_combination_ae h hcoordinates γ t s k 0 0 0 0
      have hz : n05_weakReferenceAngularJet D (fun _ => 0) (fun _ => 0) j.val := by
        intro φ hφ
        simp only [zero_mul, radialAngularMean, intervalIntegral.integral_zero, mul_zero]
      exact n05_sourceWeakJet_congr_ae hab MemLp.zero' MemLp.zero'
        (hzero 0).symm (hzero j).symm hz
  | add x y hx hy hfx hfy =>
      have hadd (k : Fin (s + 1)) :
          n05CanonicalJetSource T S C K γ t s k (x.val + y.val)
            =ᵐ[radialPhysicalMeasure D]
              (n05CanonicalJetSource T S C K γ t s k x.val +
                n05CanonicalJetSource T S C K γ t s k y.val) := by
        simpa only [one_smul, one_mul, Pi.add_def] using
          n05CanonicalJetSource_linear_combination_ae h hcoordinates γ t s k x.val y.val 1 1
      exact n05_sourceWeakJet_congr_ae hab
        ((hLp 0 x.val).add (hLp 0 y.val)) ((hLp j x.val).add (hLp j y.val))
        (hadd 0).symm (hadd j).symm
        (n05_weakReferenceAngularJet_add hab (hLp 0 x.val) (hLp 0 y.val)
          (hLp j x.val) (hLp j y.val) hfx hfy)
  | smul c x hx hfx =>
      have hsmul (k : Fin (s + 1)) :
          n05CanonicalJetSource T S C K γ t s k (c • x.val)
            =ᵐ[radialPhysicalMeasure D]
              (fun p => c * n05CanonicalJetSource T S C K γ t s k x.val p) := by
        simpa only [zero_smul, add_zero, zero_mul] using
          n05CanonicalJetSource_linear_combination_ae h hcoordinates γ t s k x.val x.val c 0
      exact n05_sourceWeakJet_congr_ae hab
        ((hLp 0 x.val).const_mul c) ((hLp j x.val).const_mul c)
        (hsmul 0).symm (hsmul j).symm (n05_weakReferenceAngularJet_const_mul hfx c)

include h hcoordinates hD hT hγw hgap M in
/-- Actual graph density closes the physical weak identity in the same
source representatives, for every finite canonical angular order. -/
theorem n05CanonicalJetSource_weak (s : ℕ) (j : Fin (s + 1))
    (v : n05CanonicalClosedSubmodule S K s) :
    n05_weakReferenceAngularJet D (n05CanonicalJetSource T S C K γ t s 0 v.val)
      (n05CanonicalJetSource T S C K γ t s j v.val) j.val := by
  obtain ⟨u, hu, huv⟩ := mem_closure_iff_seq_limit.mp
    (n05CanonicalSmoothCoreSubmodule_dense S K s v)
  have hraw : Tendsto (fun n => (u n).val) atTop (𝓝 v.val) :=
    (((n05CanonicalClosedSubmodule S K s).subtypeL.continuous.tendsto v).comp huv)
  obtain ⟨h0n, h0, ht0⟩ :=
    n05CanonicalJetSource_tendsto_physical h hcoordinates hD hT hγw hgap t M s 0 hraw
  obtain ⟨hjn, hj, htj⟩ :=
    n05CanonicalJetSource_tendsto_physical h hcoordinates hD hT hγw hgap t M s j hraw
  exact n05_weakReferenceAngularJet_of_L2_tendsto hD.choose_spec.1.2.1.le
    h0n hjn h0 hj ht0 htj
    (fun n => n05CanonicalJetSource_smooth_core_weak
      h hcoordinates hD hT hγw hgap t M s j (u n) (hu n))

include h hcoordinates hD hT hγw hgap in
/-- Every actual volume element has all its physical angular weak jets
in the same fixed weaker source space. The common constant is chosen
before the angular order, and the underlying source is the fixed lift. -/
theorem n05CanonicalSourceLift_allAngularJets
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V) :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : ℕ) (v : V.level γ t s) (j : Fin (s + 1)),
      SourceDerivativeMember D γw M (n05CanonicalJetSource T S C K γ t s j v.val) ∧
      sourceNormSquare D γw M (n05CanonicalJetSource T S C K γ t s j v.val, 0) ≤
        B * ‖v‖ ^ 2 ∧
      n05_weakReferenceAngularJet D (n05CanonicalSourceLift S C K (V.forget γ t s v))
        (n05CanonicalJetSource T S C K γ t s j v.val) j.val := by
  obtain ⟨B, hB, hb⟩ :=
    n05CanonicalJetSource_reference_bound h hcoordinates hD hT hγw.le hgap t M
  refine ⟨B, hB, fun s v j => ⟨(hb s j v.val).1, (hb s j v.val).2, ?_⟩⟩
  have hv : v.val ∈ canonicalVolumeGraph S K s := by
    rw [← hV.1 γ t s]
    exact v.property
  let w : n05CanonicalClosedSubmodule S K s := ⟨v.val, by
    rw [← SetLike.mem_coe, n05CanonicalClosedSubmodule_carrier]
    exact hv⟩
  have hw := n05CanonicalJetSource_weak h hcoordinates hD hT hγw hgap t M s j w
  have hzero := n05CanonicalJetSource_zero_ae h hcoordinates hV γ t s v
  exact n05_sourceWeakJet_congr_ae hD.choose_spec.1.2.1.le
    (r11b_sourceDerivative_memLp hD hγw (hb s 0 v.val).1)
    (r11b_sourceDerivative_memLp hD hγw (hb s j v.val).1)
    hzero Filter.EventuallyEq.rfl hw

end ContinuousFlexibility.Statements
