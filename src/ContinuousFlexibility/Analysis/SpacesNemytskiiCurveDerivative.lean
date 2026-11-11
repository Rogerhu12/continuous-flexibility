import ContinuousFlexibility.Analysis.SpacesNemytskiiMajorants
import ContinuousFlexibility.Analysis.SpacesNemytskiiParameter
import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative
import ContinuousFlexibility.Analysis.ProjectiveDifferential

/-!
# Actual projective derivatives of the composition kernels

The affine parameter derivatives have a common L² majorant on a real
interval. Dominated differentiation gives derivatives of the actual L²
classes, and hence of every closed Hilbert level and the projective limit.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology

theorem spaces_hasDerivAt_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) {f : ℝ → S} {df : S} {t : ℝ}
    (hf : HasDerivAt (fun r => (f r : E)) (df : E) t) : HasDerivAt f df t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  rw [tendsto_subtype_rng]
  exact hasDerivAt_iff_tendsto_slope_zero.mp hf

theorem spaces_hasDerivAt_piLp {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {f : ℝ → PiLp 2 E} {df : PiLp 2 E} {t : ℝ}
    (hf : ∀ i, HasDerivAt (fun r => f r i) (df i) t) : HasDerivAt f df t := by
  have hp : HasDerivAt (fun r => fun i => f r i) (fun i => df i) t := hasDerivAt_pi.mpr hf
  exact ((PiLp.continuousLinearEquiv 2 ℝ E).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hp

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
  (hI : HasInterpolation (spacesPhysicalGrading hT))
  {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
  (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)

def spacesNemytskiiJetLp (k a b c : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) : CylinderL2 :=
  (spacesNemytskiiMaterial_memLp hT hI hγ hF hF0 hFb k a b c u v).toLp
    (fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b (spacesNemytskiiMaterial hT γ F k u v) p)

theorem spacesNemytskiiJetLp_affine_hasDerivAt (k a b c : ℕ)
    (u w : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) (t₀ : ℝ) :
    HasDerivAt (fun t => spacesNemytskiiJetLp hT hI hγ hF hF0 hFb k a b c (u + t • w) v)
      (spacesNemytskiiJetLp hT hI hγ hF hF0 hFb (k + 1) a b c (u + t₀ • w) (Fin.cons w v)) t₀ := by
  obtain ⟨g, hg, hbound⟩ := spaces_nemytskii_material_jet_affine_majorant hT hγ hF hFb
    k a b c u w (Fin.cons w v) (show 0 ≤ |t₀| + 1 by positivity)
  unfold spacesNemytskiiJetLp
  apply spaces_hasDerivAt_toLp_of_dominated_deriv
    (df := fun t p => T.M (T.radius p.1) ^ c * mixedDerivative a b
      (spacesNemytskiiMaterial hT γ F (k + 1) (u + t • w) (Fin.cons w v)) p) (t₀ := t₀)
    (fun t => spacesNemytskiiMaterial_memLp hT hI hγ hF hF0 hFb k a b c (u + t • w) v)
    (spacesNemytskiiMaterial_memLp hT hI hγ hF hF0 hFb (k + 1) a b c (u + t₀ • w) (Fin.cons w v))
    (by norm_num : (0 : ℝ) < 1) hg
  · filter_upwards [] with p t ht
    exact spacesNemytskiiMaterial_weightedJet_affine_hasDerivAt hT γ hF k a b c u w v t p
  · filter_upwards [] with p t ht
    apply hbound t _ p
    exact abs_le.mpr ⟨by linarith [neg_abs_le t₀, ht.1], by linarith [le_abs_self t₀, ht.2]⟩

theorem spacesNemytskiiKernel_level_ae (k : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) (s : ℕ) (j : JetIndex s) :
    (((((spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v).val s).val j)) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      fun p => T.M (T.radius p.1) ^ (j.val 2).val * mixedDerivative (j.val 0).val (j.val 1).val
        (spacesNemytskiiMaterial hT γ F k u v) p := by
  have h := spacesPhysicalHeightEncode_ae hT
    (spacesNemytskiiPhysical_heightMember hT hI hγ hF hF0 hFb k u v) s j
  change (((((spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v).val s).val j)) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
    (fun p => T.M (T.radius p.1) ^ (j.val 2).val * mixedDerivative (j.val 0).val (j.val 1).val
      (materialPullback T γ (spacesNemytskiiPhysical hT γ F k u v)) p) at h
  rwa [spacesNemytskiiPhysical_pullback] at h

theorem spacesNemytskiiKernel_level (k : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) (s : ℕ) (j : JetIndex s) :
    (((spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v).val s).val j) =
      spacesNemytskiiJetLp hT hI hγ hF hF0 hFb k (j.val 0).val (j.val 1).val (j.val 2).val u v := by
  apply Lp.ext
  exact (spacesNemytskiiKernel_level_ae hT hI hγ hF hF0 hFb k u v s j).trans
    (MemLp.coeFn_toLp _).symm

theorem spacesNemytskiiKernel_hasProjectiveLineDerivAt (k : ℕ)
    (u w : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    HasProjectiveLineDerivAt (fun x => spacesNemytskiiKernel hT hI hγ hF hF0 hFb k x v)
      (spacesNemytskiiKernel hT hI hγ hF hF0 hFb (k + 1) u (Fin.cons w v)) u w := by
  apply (hasProjectiveLineDerivAt_iff_levels _ _ _ _).mpr
  intro s
  apply spaces_hasDerivAt_submodule (physicalJetClosedSubmodule hT s)
  apply spaces_hasDerivAt_piLp
  intro j
  simpa only [spacesNemytskiiKernel_level, zero_smul, add_zero] using
    spacesNemytskiiJetLp_affine_hasDerivAt hT hI hγ hF hF0 hFb k
      (j.val 0).val (j.val 1).val (j.val 2).val u w v 0

end ContinuousFlexibility.Statements
