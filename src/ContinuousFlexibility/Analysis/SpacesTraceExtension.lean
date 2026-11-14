module

public import ContinuousFlexibility.Analysis.SpacesTracePacketEstimates
public import ContinuousFlexibility.Analysis.SpacesPhysicalDecode

/-!
# The actual right inverse of the sample trace

The locally finite material packets are restored to the physical annulus.
They interpolate the prescribed sample values exactly, and their full
physical norms are controlled by circle norms with one fixed loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData}
variable (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)

def spacesTraceNormalizeLinear (γ : ℝ) : (ℕ → ℝ → ℝ) →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun := spacesTraceNormalized (T := T) γ
  map_add' := by intro f g; ext m θ; exact mul_add _ _ _
  map_smul' := by
    intro c f
    ext m θ
    change T.H (T.sample m) ^ (-γ) * (c * f m θ) = c * (T.H (T.sample m) ^ (-γ) * f m θ)
    ring

def spacesTracePushforwardLinear (γ : ℝ) : (PolarPoint → ℝ) →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := spacesPhysicalPushforward (D := D) (T := T) γ
  map_add' := by
    intro f g
    funext p
    by_cases hp : p ∈ annularOpen D
    · simp only [spacesPhysicalPushforward, hp, ite_true, Pi.add_apply, mul_add]
    · simp only [spacesPhysicalPushforward, hp, ite_false, Pi.add_apply, add_zero]
  map_smul' := by
    intro c f
    funext p
    by_cases hp : p ∈ annularOpen D
    · simp only [spacesPhysicalPushforward, hp, ite_true, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring
    · simp only [spacesPhysicalPushforward, hp, ite_false, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, mul_zero]

def spacesTraceExtensionRawLinear (γ : ℝ) : (ℕ → ℝ → ℝ) →ₗ[ℝ] (PolarPoint → ℝ) :=
  (spacesTracePushforwardLinear (D := D) (T := T) γ).comp
    ((spacesTracePacketLinear (spaces_trace_center T) (spacesTraceRadius hD hT)
      (spacesTraceRadius_pos hD hT) (spacesTraceRadius_locallyFinite hD hT)).comp
      (spacesTraceNormalizeLinear (T := T) γ))

theorem spacesTraceExtensionRawLinear_apply (γ : ℝ) (f : ℕ → ℝ → ℝ) :
    spacesTraceExtensionRawLinear hD hT γ f =
      spacesPhysicalPushforward (D := D) (T := T) γ (spacesTraceMaterialExtension hD hT γ f) := rfl

theorem spacesTraceExtensionRawLinear_pullback (γ : ℝ) (f : ℕ → ℝ → ℝ) :
    materialPullback T γ (spacesTraceExtensionRawLinear hD hT γ f) =
      spacesTraceMaterialExtension hD hT γ f :=
  spacesPhysicalPushforward_pullback hT γ _

theorem spacesTraceExtensionRawLinear_weightedJet (γ : ℝ) (f : ℕ → ℝ → ℝ) (a b c : ℕ) :
    weightedPhysicalJet T γ a b c (spacesTraceExtensionRawLinear hD hT γ f) =
      fun p => T.M (T.radius p.1) ^ c *
        mixedDerivative a b (spacesTraceMaterialExtension hD hT γ f) p := by
  unfold weightedPhysicalJet
  rw [spacesTraceExtensionRawLinear_pullback]

theorem spacesTraceExtensionRawLinear_sample (γ : ℝ) (f : ℕ → ℝ → ℝ) (m : ℕ) (θ : ℝ) :
    spacesTraceExtensionRawLinear hD hT γ f (T.sample m, θ) = f m θ := by
  have hs := spaces_trace_sample_mem hD hT m
  have hH : 0 < T.H (T.sample m) := (hT.2.1 _ hs).2.1
  have hp : (T.sample m, θ) ∈ annularOpen D := ⟨hs, mem_univ _⟩
  rw [spacesTraceExtensionRawLinear_apply]
  simp only [spacesPhysicalPushforward, hp, ite_true]
  change T.H (T.sample m) ^ γ *
    spacesTraceMaterialExtension hD hT γ f (spaces_trace_center T m, θ) = _
  rw [spacesTraceMaterialExtension_center, ← mul_assoc, ← Real.rpow_add hH,
    add_neg_cancel, Real.rpow_zero, one_mul]

theorem spacesTraceExtensionRawLinear_heightMember {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) (heven : ∀ m θ, f m (-θ) = f m θ) :
    HeightMember D T γ (spacesTraceExtensionRawLinear hD hT γ f) := by
  classical
  refine ⟨spacesPhysicalPushforward_contDiffOn hT γ
    (spacesTraceMaterialExtension_contDiff hD hT hf), ?_, ?_, ?_, ?_⟩
  · intro r θ
    have he : ((r, -θ) : PolarPoint) ∈ annularOpen D ↔ ((r, θ) : PolarPoint) ∈ annularOpen D := by
      simp only [annularOpen, mem_prod, mem_univ, and_true]
    simp only [spacesTraceExtensionRawLinear_apply, spacesPhysicalPushforward, he,
      spacesTraceMaterialExtension_even hD hT γ heven]
  · intro p
    have he : p + (0, Real.pi) ∈ annularOpen D ↔ p ∈ annularOpen D := by
      simp only [annularOpen, mem_prod, Prod.fst_add, Prod.snd_add, add_zero, mem_univ, and_true]
    have hp := spacesTraceMaterialExtension_periodic hD hT hf (T.rho p.1, p.2)
    simp only [Prod.mk_add_mk, add_zero] at hp
    simp only [spacesTraceExtensionRawLinear_apply, spacesPhysicalPushforward, he, Prod.fst_add,
      Prod.snd_add, add_zero, hp]
  · intro p hp
    exact ite_eq_right hp
  · intro a b c
    obtain ⟨_, _, hbound⟩ := spacesTraceMaterialExtension_jet_bound hD hT
    have h := (hbound γ f hf (b + c + 3) a b c le_rfl).1
    rw [spacesTraceExtensionRawLinear_weightedJet]
    exact h

/-- Quantitative norm control for the full extension, including every
derivative and weight in the prescribed physical norm. -/
theorem spacesTraceExtensionRawLinear_norm_bound :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (γ : ℝ) (f : ℕ → ℝ → ℝ), CircleMember T γ f →
        ∀ s, physicalNorm T γ s (spacesTraceExtensionRawLinear hD hT γ f) ≤
          C s * circleNorm T γ (s + 3) f := by
  obtain ⟨A, hA, hbound⟩ := spacesTraceMaterialExtension_jet_bound hD hT
  let C (s : ℕ) := Real.sqrt (∑ j : JetIndex s, (A (j.val 0).val (j.val 2).val) ^ 2)
  refine ⟨C, fun _ => Real.sqrt_nonneg _, fun γ f hf s => ?_⟩
  let a (j : JetIndex s) := eLpNorm
    (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
      (spacesTraceExtensionRawLinear hD hT γ f)) 2 materialCylinderMeasure
  have hj (j : JetIndex s) :
      MemLp (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
        (spacesTraceExtensionRawLinear hD hT γ f)) 2 materialCylinderMeasure ∧
      (a j).toReal ≤ A (j.val 0).val (j.val 2).val * circleNorm T γ (s + 3) f := by
    have hs := j.property
    dsimp only [a]
    rw [spacesTraceExtensionRawLinear_weightedJet]
    exact hbound γ f hf (s + 3) (j.val 0).val (j.val 1).val (j.val 2).val (by omega)
  have hsum : (∑ j : JetIndex s, a j ^ 2).toReal = ∑ j : JetIndex s, (a j).toReal ^ 2 := by
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.pow_ne_top (hj j).1.eLpNorm_ne_top)]
    simp only [ENNReal.toReal_pow]
    rfl
  change Real.sqrt (∑ j : JetIndex s, a j ^ 2).toReal ≤ _
  rw [hsum]
  calc
    Real.sqrt (∑ j : JetIndex s, (a j).toReal ^ 2) ≤
        Real.sqrt (∑ j : JetIndex s,
          (A (j.val 0).val (j.val 2).val * circleNorm T γ (s + 3) f) ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ ENNReal.toReal_nonneg (hj j).2 2)
    _ = C s * circleNorm T γ (s + 3) f := by
      simp only [mul_pow, ← Finset.sum_mul]
      have hn : 0 ≤ circleNorm T γ (s + 3) f := Real.sqrt_nonneg _
      rw [Real.sqrt_mul (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
        Real.sqrt_sq hn]

end ContinuousFlexibility.Statements
