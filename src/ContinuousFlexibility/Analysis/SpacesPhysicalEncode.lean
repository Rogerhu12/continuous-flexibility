import ContinuousFlexibility.Analysis.SpacesCylinderIntegration
import ContinuousFlexibility.Analysis.PhysicalJetBonding

/-!
# Encoding every height member in the actual physical weak graph

All coordinates are the prescribed weighted mixed derivatives as actual
`L²` classes. The smooth cylinder integration-by-parts identity proves
graph membership, and coordinate deletion proves projective compatibility.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}

theorem spaces_materialPullback_memLp (hf : HeightMember D T γ f) :
    MemLp (materialPullback T γ f) 2 materialCylinderMeasure := by
  simpa only [spaces_mixedDerivative_zero] using
    heightMember_materialPullback_mixedDerivative_memLp hf 0 0

/-- The exact weighted jet vector of a height member. -/
def spacesPhysicalHeightJet (hf : HeightMember D T γ f) (s : ℕ) : PhysicalJetHilbert s :=
  WithLp.toLp 2 (fun j : JetIndex s =>
    (hf.2.2.2.2 (j.val 0).val (j.val 1).val (j.val 2).val).toLp
      (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f))

theorem spacesPhysicalHeightJet_apply (hf : HeightMember D T γ f) (s : ℕ) (j : JetIndex s) :
    spacesPhysicalHeightJet hf s j =
      (hf.2.2.2.2 (j.val 0).val (j.val 1).val (j.val 2).val).toLp
        (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f) :=
by
  simp only [spacesPhysicalHeightJet, PiLp.toLp_apply]

theorem spacesPhysicalHeightJet_ae (hf : HeightMember D T γ f) (s : ℕ) (j : JetIndex s) :
    (spacesPhysicalHeightJet hf s j : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f := by
  rw [spacesPhysicalHeightJet_apply]
  exact MemLp.coeFn_toLp _

theorem spacesPhysicalHeightJet_zero (hf : HeightMember D T γ f) (s : ℕ) :
    spacesPhysicalHeightJet hf s (zeroJetIndex s) =
      (spaces_materialPullback_memLp hf).toLp (materialPullback T γ f) := by
  apply Lp.ext
  filter_upwards [spacesPhysicalHeightJet_ae hf s (zeroJetIndex s),
    (spaces_materialPullback_memLp hf).coeFn_toLp] with p hp hq
  rw [hq]
  simpa only [zeroJetIndex, Fin.val_zero, weightedPhysicalJet, pow_zero,
    one_mul, spaces_mixedDerivative_zero] using hp

/-- Even periodic heights have the required reflected cylinder symmetry. -/
theorem spaces_materialPullback_reflection (hf : HeightMember D T γ f) (p : PolarPoint) :
    materialPullback T γ f (p.1, Real.pi - p.2) = materialPullback T γ f p := by
  have he : materialPullback T γ f (p.1, -p.2) = materialPullback T γ f p := by
    simp only [materialPullback, hf.2.1]
  have hp := materialPullback_angular_periodic (T := T) (γ := γ) hf.2.2.1 p.1 (-p.2)
  change materialPullback T γ f (p.1, -p.2 + Real.pi) = materialPullback T γ f (p.1, -p.2) at hp
  rw [show Real.pi - p.2 = -p.2 + Real.pi by ring]
  exact hp.trans he

/-- Every exact height jet satisfies the original distributional graph. -/
theorem spacesPhysicalHeightJet_mem_graph (hT : IsMaterialData D T)
    (hf : HeightMember D T γ f) (s : ℕ) :
    spacesPhysicalHeightJet hf s ∈ physicalJetGraph T s := by
  have hfs : ContDiff ℝ ∞ (materialPullback T γ f) := contDiff_materialPullback hT hf.1
  have hfp : Function.Periodic (materialPullback T γ f) (0, Real.pi) := by
    rintro ⟨x, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using materialPullback_angular_periodic hf.2.2.1 x θ
  refine ⟨?_, fun j => ?_⟩
  · rw [spacesPhysicalHeightJet_zero]
    have hae := (spaces_materialPullback_memLp hf).coeFn_toLp
    have href := measurePreserving_cylinderAngularReflection.quasiMeasurePreserving.ae_eq_comp hae
    filter_upwards [href, hae] with p hp hq
    exact hp.trans ((spaces_materialPullback_reflection hf p).trans hq.symm)
  · let hd := heightMember_materialPullback_mixedDerivative_memLp hf (j.val 0).val (j.val 1).val
    refine ⟨hd.toLp (mixedDerivative (j.val 0).val (j.val 1).val (materialPullback T γ f)), ?_, ?_⟩
    · rw [spacesPhysicalHeightJet_zero]
      exact spaces_hasWeakMixedDerivative_of_smooth hfs hfp _ _ (spaces_materialPullback_memLp hf) hd
    · filter_upwards [spacesPhysicalHeightJet_ae hf s j, hd.coeFn_toLp] with p hp hq
      rw [hq]
      exact hp

/-- Deleting higher coordinates preserves the exact weighted jets. -/
theorem spacesPhysicalHeightJet_restrict (hf : HeightMember D T γ f)
    {s t : ℕ} (hst : s ≤ t) :
    physicalJetHilbertRestrict hst (spacesPhysicalHeightJet hf t) = spacesPhysicalHeightJet hf s := by
  apply PiLp.ext
  intro j
  rw [physicalJetHilbertRestrict_apply]
  apply Lp.ext
  filter_upwards [spacesPhysicalHeightJet_ae hf t (physicalJetIndexOfLE hst j),
    spacesPhysicalHeightJet_ae hf s j] with p hp hq
  exact hp.trans hq.symm

/-- The actual compatible sequence encoding a height member. -/
def spacesPhysicalHeightEncode (hT : IsMaterialData D T) (hf : HeightMember D T γ f) :
    PhysicalJetProjectiveLimit hT :=
  ⟨fun s => ⟨spacesPhysicalHeightJet hf s, by
    change spacesPhysicalHeightJet hf s ∈
      (physicalJetClosedSubmodule hT s : Set (PhysicalJetHilbert s))
    rw [physicalJetClosedSubmodule_carrier hT]
    exact spacesPhysicalHeightJet_mem_graph hT hf s⟩, by
    intro s
    apply Subtype.ext
    exact spacesPhysicalHeightJet_restrict hf (Nat.le_succ s)⟩

theorem spacesPhysicalHeightEncode_level (hT : IsMaterialData D T)
    (hf : HeightMember D T γ f) (s : ℕ) :
    ((spacesPhysicalHeightEncode hT hf).val s).val = spacesPhysicalHeightJet hf s := rfl

theorem spacesPhysicalHeightEncode_ae (hT : IsMaterialData D T)
    (hf : HeightMember D T γ f) (s : ℕ) (j : JetIndex s) :
    ((((spacesPhysicalHeightEncode hT hf).val s).val j) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f := by
  rw [spacesPhysicalHeightEncode_level]
  exact spacesPhysicalHeightJet_ae hf s j

theorem spacesPhysicalHeightEncode_zero_ae (hT : IsMaterialData D T)
    (hf : HeightMember D T γ f) :
    (physicalJetProjectiveZero hT (spacesPhysicalHeightEncode hT hf) : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure] materialPullback T γ f := by
  rw [physicalJetProjectiveZero_apply hT _ 0, spacesPhysicalHeightEncode_level,
    spacesPhysicalHeightJet_zero]
  exact (spaces_materialPullback_memLp hf).coeFn_toLp

end ContinuousFlexibility.Statements
