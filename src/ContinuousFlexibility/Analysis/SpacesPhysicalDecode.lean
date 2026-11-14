module

public import ContinuousFlexibility.Analysis.SpacesPhysicalReconstruction
public import ContinuousFlexibility.Analysis.SpacesPhysicalEncode
public import ContinuousFlexibility.Analysis.SpacesTracePointwise
public import ContinuousFlexibility.Analysis.CircleSmoothReconstruction

/-!
# Decoding the actual physical weak jet space

The smooth material representative is unique, even and linear in its
weak jets. Restoring the weight and radial coordinate gives exactly the
height functions and the Hilbert norms specified by the physical model.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Continuous periodic functions are determined by their cylinder class. -/
theorem spaces_cylinder_periodic_eq_of_ae_eq {f g : PolarPoint → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfp : Function.Periodic f (0, Real.pi)) (hgp : Function.Periodic g (0, Real.pi))
    (hae : f =ᵐ[materialCylinderMeasure] g) : f = g := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  rw [materialCylinderMeasure_eq_prod] at hae
  have hrows := Measure.ae_ae_of_ae_prod hae
  funext p
  have hpoint : ∀ᵐ x ∂(volume : Measure ℝ), f (x, p.2) = g (x, p.2) := by
    filter_upwards [hrows] with x hx
    have hfx : Continuous (fun θ => f (x, θ)) := hf.comp (continuous_const.prodMk continuous_id)
    have hgx : Continuous (fun θ => g (x, θ)) := hg.comp (continuous_const.prodMk continuous_id)
    have hfp' : Function.Periodic (fun θ => f (x, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hfp (x, θ)
    have hgp' : Function.Periodic (fun θ => g (x, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hgp (x, θ)
    exact congrFun (angle_periodic_eq_of_ae_eq hfx hgx hfp' hgp' hx) p.2
  exact congrFun (Measure.eq_of_ae_eq hpoint
    (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const))) p.1

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

theorem spacesPhysicalRepresentative_zero_ae (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalRepresentative hT u =ᵐ[materialCylinderMeasure]
      physicalJetProjectiveZero hT u := by
  have hi : physicalJetPureMixedIndex 0 0 = zeroJetIndex 0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  have he : physicalJetMixedDerivative u 0 0 = physicalJetProjectiveZero hT u := by
    rw [physicalJetMixedDerivative, hi, physicalJetProjectiveZero_apply hT u 0]
  have hz : mixedDerivative 0 0 (spacesPhysicalRepresentative hT u) =
      spacesPhysicalRepresentative hT u := by
    funext p
    simp only [mixedDerivative, iteratedDeriv_zero]
  simpa only [hz, he] using spacesPhysicalRepresentative_mixedDerivative_cylinder_ae hT u 0 0

theorem spacesPhysicalRepresentative_even (u : PhysicalJetProjectiveLimit hT) (r θ : ℝ) :
    spacesPhysicalRepresentative hT u (r, -θ) = spacesPhysicalRepresentative hT u (r, θ) := by
  let v := spacesPhysicalRepresentative hT u
  have hv : Continuous v := (spacesPhysicalRepresentative_contDiff hT u).continuous
  have hp : Function.Periodic v (0, Real.pi) := spacesPhysicalRepresentative_periodic hT u
  have hrefp : Function.Periodic (fun p : PolarPoint => v (p.1, Real.pi - p.2)) (0, Real.pi) := by
    intro p
    have h := hp (p.1, -p.2)
    simp only [Prod.mk_add_mk, add_zero] at h
    change v (p.1 + 0, Real.pi - (p.2 + Real.pi)) = v (p.1, Real.pi - p.2)
    rw [add_zero]
    rw [show Real.pi - (p.2 + Real.pi) = -p.2 by ring,
      show Real.pi - p.2 = -p.2 + Real.pi by ring]
    exact h.symm
  have hva := spacesPhysicalRepresentative_zero_ae hT u
  have hvar := measurePreserving_cylinderAngularReflection.quasiMeasurePreserving.ae_eq_comp hva
  have hgraph := (physicalJetProjective_mem_graph u 0).1
  rw [← physicalJetProjectiveZero_apply hT u 0] at hgraph
  have he : (fun p : PolarPoint => v (p.1, Real.pi - p.2)) = v :=
    spaces_cylinder_periodic_eq_of_ae_eq
      (hv.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd))) hv hrefp hp
      (hvar.trans (hgraph.trans hva.symm))
  have h := congrFun he (r, θ)
  have hp' := hp (r, -θ)
  simp only [Prod.mk_add_mk, add_zero] at hp'
  change v (r, Real.pi - θ) = v (r, θ) at h
  rw [show Real.pi - θ = -θ + Real.pi by ring, hp'] at h
  exact h

theorem spacesPhysicalRepresentative_add (u v : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalRepresentative hT (u + v) =
      fun p => spacesPhysicalRepresentative hT u p + spacesPhysicalRepresentative hT v p := by
  apply spaces_cylinder_periodic_eq_of_ae_eq
    (spacesPhysicalRepresentative_contDiff hT _).continuous
    ((spacesPhysicalRepresentative_contDiff hT u).continuous.add
      (spacesPhysicalRepresentative_contDiff hT v).continuous)
    (spacesPhysicalRepresentative_periodic hT _)
    ((spacesPhysicalRepresentative_periodic hT u).add (spacesPhysicalRepresentative_periodic hT v))
  have hsum := spacesPhysicalRepresentative_zero_ae hT (u + v)
  rw [map_add] at hsum
  filter_upwards [hsum, spacesPhysicalRepresentative_zero_ae hT u,
    spacesPhysicalRepresentative_zero_ae hT v,
    Lp.coeFn_add (physicalJetProjectiveZero hT u) (physicalJetProjectiveZero hT v)] with p h hu hv ha
  exact h.trans (ha.trans (congrArg₂ (· + ·) hu.symm hv.symm))

theorem spacesPhysicalRepresentative_smul (c : ℝ) (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalRepresentative hT (c • u) = fun p => c * spacesPhysicalRepresentative hT u p := by
  apply spaces_cylinder_periodic_eq_of_ae_eq
    (spacesPhysicalRepresentative_contDiff hT _).continuous
    (continuous_const.mul (spacesPhysicalRepresentative_contDiff hT u).continuous)
    (spacesPhysicalRepresentative_periodic hT _) ?_
  · have hcu := spacesPhysicalRepresentative_zero_ae hT (c • u)
    rw [map_smul] at hcu
    filter_upwards [hcu, spacesPhysicalRepresentative_zero_ae hT u,
      Lp.coeFn_smul c (physicalJetProjectiveZero hT u)] with p h hu hc
    exact h.trans (hc.trans (congrArg (c * ·) hu.symm))
  · intro p
    change c * spacesPhysicalRepresentative hT u (p + (0, Real.pi)) =
      c * spacesPhysicalRepresentative hT u p
    rw [spacesPhysicalRepresentative_periodic hT u p]

/-- Restore the physical weight on the open annulus, with the prescribed
zero representative outside it. -/
def spacesPhysicalPushforward (γ : ℝ) (v : PolarPoint → ℝ) (p : PolarPoint) : ℝ := by
  classical
  exact if p ∈ annularOpen D then T.H p.1 ^ γ * v (T.rho p.1, p.2) else 0

include hT in
theorem spacesPhysicalPushforward_pullback (γ : ℝ) (v : PolarPoint → ℝ) :
    materialPullback T γ (spacesPhysicalPushforward (D := D) (T := T) γ v) = v := by
  funext p
  have hr := hT.2.2.2.2.2.2.2.1 p.1
  have hH : 0 < T.H (T.radius p.1) := (hT.2.1 _ hr.1).2.1
  have hm : (T.radius p.1, p.2) ∈ annularOpen D := ⟨hr.1, mem_univ _⟩
  simp only [materialPullback, spacesPhysicalPushforward, ite_eq_left hm, hr.2]
  rw [← mul_assoc, ← Real.rpow_add hH, neg_add_cancel, Real.rpow_zero, one_mul]

include hT in
theorem spacesPhysicalPushforward_contDiffOn (γ : ℝ) {v : PolarPoint → ℝ}
    (hv : ContDiff ℝ ∞ v) :
    ContDiffOn ℝ ∞ (spacesPhysicalPushforward (D := D) (T := T) γ v) (annularOpen D) := by
  have hH : ContDiffOn ℝ ∞ T.H (Ioo D.a D.b) := hT.1 T.H (by simp)
  have hrho : ContDiffOn ℝ ∞ T.rho (Ioo D.a D.b) := hT.1 T.rho (by simp)
  have hH' : ContDiffOn ℝ ∞ (fun p : PolarPoint => T.H p.1) (annularOpen D) :=
    hH.comp contDiffOn_fst (fun _ hp => hp.1)
  have hrho' : ContDiffOn ℝ ∞ (fun p : PolarPoint => T.rho p.1) (annularOpen D) :=
    hrho.comp contDiffOn_fst (fun _ hp => hp.1)
  have hw : ContDiffOn ℝ ∞ (fun p : PolarPoint => T.H p.1 ^ γ) (annularOpen D) :=
    hH'.rpow_const_of_ne (fun p hp => (hT.2.1 p.1 hp.1).2.1.ne')
  have hc : ContDiffOn ℝ ∞ (fun p : PolarPoint => v (T.rho p.1, p.2)) (annularOpen D) :=
    hv.comp_contDiffOn (hrho'.prodMk contDiffOn_snd)
  apply (hw.mul hc).congr
  intro p hp
  exact ite_eq_left hp

/-- The physical height decoded from the full compatible weak jet. -/
def spacesPhysicalDecoded (γ : ℝ) (u : PhysicalJetProjectiveLimit hT) : PolarPoint → ℝ :=
  spacesPhysicalPushforward (D := D) (T := T) γ (spacesPhysicalRepresentative hT u)

theorem spacesPhysicalDecoded_pullback (γ : ℝ) (u : PhysicalJetProjectiveLimit hT) :
    materialPullback T γ (spacesPhysicalDecoded hT γ u) = spacesPhysicalRepresentative hT u :=
  spacesPhysicalPushforward_pullback hT γ _

/-- Each weighted classical derivative is exactly its prescribed Hilbert coordinate. -/
theorem spacesPhysicalDecoded_level_ae (γ : ℝ) (u : PhysicalJetProjectiveLimit hT)
    (s : ℕ) (j : JetIndex s) :
    (((u.val s).val j) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val (spacesPhysicalDecoded hT γ u) := by
  have hw := physicalJetMixedDerivative_level_ae u s j
  have hd := spacesPhysicalRepresentative_mixedDerivative_cylinder_ae hT u (j.val 0).val (j.val 1).val
  filter_upwards [hw, hd] with p hp hdp
  rw [weightedPhysicalJet, spacesPhysicalDecoded_pullback, hdp]
  exact hp

theorem spacesPhysicalDecoded_heightMember (γ : ℝ) (u : PhysicalJetProjectiveLimit hT) :
    HeightMember D T γ (spacesPhysicalDecoded hT γ u) := by
  classical
  refine ⟨spacesPhysicalPushforward_contDiffOn hT γ (spacesPhysicalRepresentative_contDiff hT u),
    ?_, ?_, ?_, ?_⟩
  · intro r θ
    have he : ((r, -θ) : PolarPoint) ∈ annularOpen D ↔ ((r, θ) : PolarPoint) ∈ annularOpen D := by
      simp only [annularOpen, mem_prod, mem_univ, and_true]
    simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, he,
      spacesPhysicalRepresentative_even hT u]
  · intro p
    have he : p + (0, Real.pi) ∈ annularOpen D ↔ p ∈ annularOpen D := by
      simp only [annularOpen, mem_prod, Prod.fst_add, Prod.snd_add, add_zero, mem_univ, and_true]
    have hp := spacesPhysicalRepresentative_periodic hT u (T.rho p.1, p.2)
    simp only [Prod.mk_add_mk, add_zero] at hp
    simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, he, Prod.fst_add,
      Prod.snd_add, add_zero, hp]
  · intro p hp
    exact ite_eq_right hp
  · intro a b c
    let j : JetIndex (a + b + c) := spaces_full_jet_index a b c (a + b + c) le_rfl
    have h := spacesPhysicalDecoded_level_ae hT γ u (a + b + c) j
    exact (memLp_congr_ae h).mp (Lp.memLp ((u.val (a + b + c)).val j))

/-- The decoded function has precisely the original physical Hilbert norm. -/
theorem spacesPhysicalDecoded_physicalNorm (γ : ℝ) (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    ‖u.val s‖ = physicalNorm T γ s (spacesPhysicalDecoded hT γ u) := by
  have he : (∑ j : JetIndex s,
      eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
        (spacesPhysicalDecoded hT γ u)) 2 materialCylinderMeasure ^ 2) =
      ENNReal.ofReal (‖u.val s‖ ^ 2) := by
    change _ = ENNReal.ofReal (‖(u.val s).val‖ ^ 2)
    rw [PiLp.norm_sq_eq_of_L2, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [← eLpNorm_congr_ae (spacesPhysicalDecoded_level_ae hT γ u s j),
      ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  rw [physicalNorm, he, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem spacesPhysicalDecoded_zero_ae (γ : ℝ) (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    (((u.val s).val (zeroJetIndex s)) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      materialPullback T γ (spacesPhysicalDecoded hT γ u) := by
  rw [spacesPhysicalDecoded_pullback, ← physicalJetProjectiveZero_apply hT u s]
  exact (spacesPhysicalRepresentative_zero_ae hT u).symm

theorem spacesPhysicalDecoded_injective (γ : ℝ) :
    Function.Injective (spacesPhysicalDecoded hT γ) := by
  intro u v huv
  apply Subtype.ext
  funext s
  apply Subtype.ext
  apply PiLp.ext
  intro j
  apply Lp.ext
  have hu := spacesPhysicalDecoded_level_ae hT γ u s j
  rw [huv] at hu
  exact hu.trans (spacesPhysicalDecoded_level_ae hT γ v s j).symm

theorem spacesPhysicalDecoded_encode {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) :
    spacesPhysicalDecoded hT γ (spacesPhysicalHeightEncode hT hf) = f := by
  have hp : Function.Periodic (materialPullback T γ f) (0, Real.pi) := by
    rintro ⟨r, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using materialPullback_angular_periodic hf.2.2.1 r θ
  have he : spacesPhysicalRepresentative hT (spacesPhysicalHeightEncode hT hf) =
      materialPullback T γ f :=
    spaces_cylinder_periodic_eq_of_ae_eq
      (spacesPhysicalRepresentative_contDiff hT _).continuous
      (contDiff_materialPullback hT hf.1).continuous (spacesPhysicalRepresentative_periodic hT _) hp
      ((spacesPhysicalRepresentative_zero_ae hT _).trans (spacesPhysicalHeightEncode_zero_ae hT hf))
  funext p
  classical
  by_cases hp : p ∈ annularOpen D
  · have hr := hT.2.2.2.2.2.2.2.2.1 p.1 hp.1
    have hH : 0 < T.H p.1 := (hT.2.1 _ hp.1).2.1
    simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, ite_eq_left hp, he,
      materialPullback, hr]
    rw [← mul_assoc, ← Real.rpow_add hH, add_neg_cancel, Real.rpow_zero, one_mul]
  · simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, ite_eq_right hp, hf.2.2.2.1 p hp]

/-- The actual decoded function depends linearly on the jet. -/
def spacesPhysicalDecodeLinear (γ : ℝ) : PhysicalJetProjectiveLimit hT →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := spacesPhysicalDecoded hT γ
  map_add' := by
    intro u v
    funext p
    classical
    by_cases hp : p ∈ annularOpen D
    · simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, ite_eq_left hp,
        spacesPhysicalRepresentative_add, Pi.add_apply, mul_add]
    · simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, ite_eq_right hp,
        Pi.add_apply, add_zero]
  map_smul' := by
    intro c u
    funext p
    classical
    by_cases hp : p ∈ annularOpen D
    · simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, ite_eq_left hp,
        spacesPhysicalRepresentative_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, ite_eq_right hp,
        Pi.smul_apply, smul_eq_mul, mul_zero]

theorem spacesPhysicalDecoded_evaluation_bound (γ : ℝ) (p : PolarPoint)
    (u : PhysicalJetProjectiveLimit hT) :
    |spacesPhysicalDecoded hT γ u p| ≤
      (|T.H p.1 ^ γ| * (4 * Real.sqrt Real.pi)) *
        Analysis.gradedSeminorm (fun s => physicalJetClosedSubmodule hT s) (physicalJetBond hT) 2 u := by
  have hC : 0 ≤ |T.H p.1 ^ γ| * (4 * Real.sqrt Real.pi) := by positivity
  classical
  by_cases hp : p ∈ annularOpen D
  · have hb := spaces_materialPullback_bound hT (spacesPhysicalDecoded_heightMember hT γ u)
      (T.rho p.1, p.2)
    rw [spacesPhysicalDecoded_pullback, ← spacesPhysicalDecoded_physicalNorm] at hb
    calc
      |spacesPhysicalDecoded hT γ u p| =
          |T.H p.1 ^ γ| * |spacesPhysicalRepresentative hT u (T.rho p.1, p.2)| := by
        simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, ite_eq_left hp, abs_mul]
      _ ≤ |T.H p.1 ^ γ| * ((4 * Real.sqrt Real.pi) * ‖u.val 2‖) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = (|T.H p.1 ^ γ| * (4 * Real.sqrt Real.pi)) * ‖u.val 2‖ := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Analysis.norm_coordinate_le_graded _ _ (le_refl 2) u) hC
  · simp only [spacesPhysicalDecoded, spacesPhysicalPushforward, ite_eq_right hp, abs_zero]
    exact mul_nonneg hC (apply_nonneg _ _)

/-- Evaluation is continuous in the original projective topology. -/
def spacesPhysicalDecodeCLM (γ : ℝ) : PhysicalJetProjectiveLimit hT →L[ℝ] (PolarPoint → ℝ) where
  toLinearMap := spacesPhysicalDecodeLinear hT γ
  cont := by
    apply continuous_pi
    intro p
    let L : PhysicalJetProjectiveLimit hT →ₗ[ℝ] ℝ :=
      (LinearMap.proj p).comp (spacesPhysicalDecodeLinear hT γ)
    change Continuous L
    apply (Analysis.withSeminorms_graded _ _).continuous_real_rng
    refine ⟨{2}, ⟨|T.H p.1 ^ γ| * (4 * Real.sqrt Real.pi), by positivity⟩, fun u => ?_⟩
    simp only [Finset.sup_singleton, smul_apply, NNReal.smul_def, smul_eq_mul]
    exact (le_abs_self (spacesPhysicalDecoded hT γ u p)).trans
      (spacesPhysicalDecoded_evaluation_bound hT γ p u)

/-- The canonical Sobolev model uses the exact closed weak graphs. -/
def canonicalSobolevModelData (γ : ℝ) : SobolevModelData where
  level := physicalJetClosedSubmodule hT
  bond := physicalJetBond hT
  decode := (spacesPhysicalDecodeCLM hT γ).toLinearMap

theorem canonicalSobolevModelData_decode (γ : ℝ) (u : (canonicalSobolevModelData hT γ).Space) :
    (canonicalSobolevModelData hT γ).decode u = spacesPhysicalDecoded hT γ u := rfl

theorem isSobolevModel_canonicalSobolevModelData (γ : ℝ) :
    IsSobolevModel D T γ (canonicalSobolevModelData hT γ) := by
  refine ⟨physicalJetClosedSubmodule_carrier hT, isClosed_physicalJetClosedSubmodule hT,
    (spacesPhysicalDecodeCLM hT γ).continuous, spacesPhysicalDecoded_heightMember hT γ,
    fun f hf => ⟨spacesPhysicalHeightEncode hT hf, spacesPhysicalDecoded_encode hT hf⟩,
    spacesPhysicalDecoded_injective hT γ, spacesPhysicalDecoded_zero_ae hT γ,
    spacesPhysicalDecoded_physicalNorm hT γ⟩

include hT in
theorem exists_isSobolevModel_of_materialData (γ : ℝ) :
    ∃ H : SobolevModelData, IsSobolevModel D T γ H :=
  ⟨canonicalSobolevModelData hT γ, isSobolevModel_canonicalSobolevModelData hT γ⟩

end ContinuousFlexibility.Statements
