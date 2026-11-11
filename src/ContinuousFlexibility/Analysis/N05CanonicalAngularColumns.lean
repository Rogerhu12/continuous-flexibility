import ContinuousFlexibility.Analysis.N05CanonicalAngularSourceBounds
import ContinuousFlexibility.Analysis.N05CanonicalLpMaps

/-!
# Continuous canonical jet columns and their fixed physical sources

Each angular coordinate is a contraction from the actual Hilbert jet
space. Its unsigned physical lift has a source bound independent of the
number of retained jets. On the volume graph, the zero column agrees
almost everywhere with the already fixed source lift.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

def n05CanonicalAngularColumn (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (j : Fin (s + 1)) :
    CanonicalVolumeJets S K s →L[ℝ] CanonicalL2Sequence S K :=
  n05LpMapCLM
    (fun m => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) j).toLinearMap)
    1 zero_le_one (fun m x => by
      simpa only [ContinuousLinearMap.coe_coe, PiLp.proj_apply, one_mul] using
        PiLp.norm_apply_le x j)

@[simp] theorem n05CanonicalAngularColumn_apply (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (j : Fin (s + 1))
    (v : CanonicalVolumeJets S K s) (m : ℕ) :
    n05CanonicalAngularColumn S K s j v m = v m j := by
  simp only [n05CanonicalAngularColumn, n05LpMapCLM_apply,
    ContinuousLinearMap.coe_coe, PiLp.proj_apply]

theorem n05CanonicalAngularColumn_bound (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (j : Fin (s + 1)) (v : CanonicalVolumeJets S K s) :
    ‖n05CanonicalAngularColumn S K s j v‖ ≤ ‖v‖ := by
  unfold n05CanonicalAngularColumn
  simpa only [one_mul] using n05LpMapCLM_bound
    (fun m => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) j).toLinearMap)
    1 zero_le_one (fun m x => by
      simpa only [ContinuousLinearMap.coe_coe, PiLp.proj_apply, one_mul] using
        PiLp.norm_apply_le x j) v

theorem n05CanonicalAngularColumn_single (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (j : Fin (s + 1)) (m : ℕ)
    (v : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) :
    n05CanonicalAngularColumn S K s j (lp.single 2 m v) = lp.single 2 m (v j) := by
  classical
  apply lp.ext
  funext k
  rw [n05CanonicalAngularColumn_apply]
  by_cases hkm : k = m
  · subst k
    simp only [lp.single_apply_self]
  · simp only [lp.single_apply_ne 2 m _ hkm, PiLp.zero_apply]

def n05CanonicalJetSource (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (γ t : ℝ)
    (s : ℕ) (j : Fin (s + 1)) (v : CanonicalVolumeJets S K s) : PolarPoint → ℝ :=
  n05CanonicalAngularSource T S C K γ t (n05CanonicalAngularColumn S K s j v)

theorem n05CanonicalJetSource_periodic (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (γ t : ℝ)
    (s : ℕ) (j : Fin (s + 1)) (v : CanonicalVolumeJets S K s) :
    Function.Periodic (n05CanonicalJetSource T S C K γ t s j v) (0, Real.pi) :=
  n05CanonicalAngularSource_periodic T S C K γ t _

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
theorem n05CanonicalJetSource_source_ae (γ t : ℝ) (s : ℕ) (j : Fin (s + 1))
    (v : CanonicalVolumeJets S K s) (m : ℕ) :
    (fun p => n05CanonicalSampleWeight T S K γ t m * v m j p)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        (n05CanonicalJetSource T S C K γ t s j v) := by
  simpa only [n05CanonicalJetSource, n05CanonicalAngularColumn_apply] using
    n05CanonicalAngularSource_source_ae h hcoordinates γ t
      (n05CanonicalAngularColumn S K s j v) m

include h hcoordinates in
theorem n05CanonicalJetSource_zero_ae {V : VolumeModelData S K}
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ) (v : V.level γ t s) :
    n05CanonicalJetSource T S C K γ t s 0 v.val =ᵐ[radialPhysicalMeasure D]
      n05CanonicalSourceLift S C K (V.forget γ t s v) := by
  have he : (fun m => n05CanonicalSampleWeight T S K γ t m •
      n05CanonicalAngularColumn S K s 0 v.val m) = V.forget γ t s v := by
    funext m
    rw [n05CanonicalAngularColumn_apply, hV.2.2.2 γ t s v m]
    rfl
  unfold n05CanonicalJetSource n05CanonicalAngularSource
  rw [he]
  exact n05CanonicalAngularLift_eq_sourceLift_ae h hcoordinates (V.forget γ t s v)
    (n05_volumeMember_reflection hV (show VolumeMember S K V γ t s (V.forget γ t s v)
      from ⟨v, rfl⟩))

include h hcoordinates in
theorem n05CanonicalJetSource_linear_combination_ae (γ t : ℝ) (s : ℕ)
    (j : Fin (s + 1)) (v w : CanonicalVolumeJets S K s) (c d : ℝ) :
    n05CanonicalJetSource T S C K γ t s j (c • v + d • w) =ᵐ[radialPhysicalMeasure D]
      (fun p => c * n05CanonicalJetSource T S C K γ t s j v p +
        d * n05CanonicalJetSource T S C K γ t s j w p) := by
  simpa only [n05CanonicalJetSource, map_add, map_smul] using
    n05CanonicalAngularSource_linear_combination_ae h hcoordinates γ t
      (n05CanonicalAngularColumn S K s j v) (n05CanonicalAngularColumn S K s j w) c d

variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)

include h hcoordinates hD hT in
/-- One constant works for all retained angular orders and all columns. -/
theorem n05CanonicalJetSource_reference_bound
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : ℕ) (j : Fin (s + 1)) (v : CanonicalVolumeJets S K s),
      SourceDerivativeMember D γw M (n05CanonicalJetSource T S C K γ t s j v) ∧
      sourceNormSquare D γw M (n05CanonicalJetSource T S C K γ t s j v, 0) ≤
        B * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05CanonicalAngularSource_reference_bound h hcoordinates hD hT hγw hgap t M
  refine ⟨B, hB, fun s j v => ⟨(hb _).1, (hb _).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (n05CanonicalAngularColumn_bound S K s j v) 2) hB.le

include h hcoordinates hD hT in
theorem n05CanonicalJetSource_tendsto_physical
    {γw γ : ℝ} (hγw : 0 < γw) (hgap : γw < γ) (t M : ℝ)
    (s : ℕ) (j : Fin (s + 1))
    {v : ℕ → CanonicalVolumeJets S K s} {w : CanonicalVolumeJets S K s}
    (hvw : Tendsto v atTop (𝓝 w)) :
    ∃ hv : ∀ n, MemLp (n05CanonicalJetSource T S C K γ t s j (v n)) 2
        (radialPhysicalMeasure D),
      ∃ hw : MemLp (n05CanonicalJetSource T S C K γ t s j w) 2
          (radialPhysicalMeasure D),
        Tendsto (fun n => (hv n).toLp (n05CanonicalJetSource T S C K γ t s j (v n)))
          atTop (𝓝 (hw.toLp (n05CanonicalJetSource T S C K γ t s j w))) :=
  n05CanonicalAngularSource_tendsto_physical h hcoordinates hD hT hγw hgap t M
    (((n05CanonicalAngularColumn S K s j).continuous.tendsto w).comp hvw)

end ContinuousFlexibility.Statements
