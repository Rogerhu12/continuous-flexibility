import ContinuousFlexibility.Analysis.ProjectiveJets
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-!
# Compact parameter integration in the actual projective limit

The integral is taken in each complete Banach coordinate. Bonding maps
commute with these integrals, so the result is an element of the existing
projective limit. Joint continuity and multilinearity are proved in its
original product topology; no norm is imposed on the parameter space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
  [∀ n, NormedSpace ℝ (F n)] [∀ n, CompleteSpace (F n)]
  {bond : ∀ n, F (n + 1) →L[ℝ] F n}

def projectiveUnitIntegral (f : ℝ → ProjectiveLimit F bond) (hf : Continuous f) :
    ProjectiveLimit F bond :=
  ⟨fun n => ∫ a in (0 : ℝ)..1, (f a).val n, by
    intro n
    have hi : IntervalIntegrable (fun a => (f a).val (n + 1)) volume 0 1 :=
      ((projectiveCoordinate F bond (n + 1)).continuous.comp hf).intervalIntegrable 0 1
    rw [← (bond n).intervalIntegral_comp_comm hi]
    exact intervalIntegral.integral_congr fun a _ => (f a).property n⟩

theorem projectiveUnitIntegral_coordinate
    (f : ℝ → ProjectiveLimit F bond) (hf : Continuous f) (n : ℕ) :
    (projectiveUnitIntegral f hf).val n = ∫ a in (0 : ℝ)..1, (f a).val n := rfl

theorem projectiveUnitIntegral_congr
    {f g : ℝ → ProjectiveLimit F bond} (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ a ∈ Icc (0 : ℝ) 1, f a = g a) :
    projectiveUnitIntegral f hf = projectiveUnitIntegral g hg := by
  apply Subtype.ext
  funext n
  apply intervalIntegral.integral_congr
  intro a ha
  rw [heq a (by simpa only [uIcc_of_le zero_le_one] using ha)]

theorem projectiveUnitIntegral_add
    {f g : ℝ → ProjectiveLimit F bond} (hf : Continuous f) (hg : Continuous g) :
    projectiveUnitIntegral (fun a => f a + g a) (hf.add hg) =
      projectiveUnitIntegral f hf + projectiveUnitIntegral g hg := by
  apply Subtype.ext
  funext n
  change (∫ a in (0 : ℝ)..1, (f a).val n + (g a).val n) = _
  exact intervalIntegral.integral_add
    (((projectiveCoordinate F bond n).continuous.comp hf).intervalIntegrable 0 1)
    (((projectiveCoordinate F bond n).continuous.comp hg).intervalIntegrable 0 1)

theorem projectiveUnitIntegral_smul
    {f : ℝ → ProjectiveLimit F bond} (hf : Continuous f) (c : ℝ) :
    projectiveUnitIntegral (fun a => c • f a) (hf.const_smul c) =
      c • projectiveUnitIntegral f hf := by
  apply Subtype.ext
  funext n
  change (∫ a in (0 : ℝ)..1, c • (f a).val n) = _
  exact intervalIntegral.integral_smul c _

theorem continuous_projectiveUnitIntegral
    {X : Type*} [TopologicalSpace X] {f : X → ℝ → ProjectiveLimit F bond}
    (hf : Continuous (fun p : X × ℝ => f p.1 p.2)) :
    Continuous (fun x => projectiveUnitIntegral (f x)
      (hf.comp (continuous_const.prodMk continuous_id))) := by
  have hc (n : ℕ) : Continuous
      (fun x => ∫ a in (0 : ℝ)..1, (f x a).val n) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (projectiveCoordinate F bond n).continuous.comp hf
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, tendsto_projectiveLimit_iff]
  exact fun n => (hc n).tendsto x

theorem projectiveUnitIntegral_grading_le
    {f : ℝ → ProjectiveLimit F bond} (hf : Continuous f)
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a ∈ Icc (0 : ℝ) 1, gradedSeminorm F bond n (f a) ≤ C) :
    gradedSeminorm F bond n (projectiveUnitIntegral f hf) ≤ C := by
  apply (gradedSeminorm_le_iff F bond n _ hC).mpr
  intro i hi
  have hb : ∀ a ∈ uIoc (0 : ℝ) 1, ‖(f a).val i‖ ≤ C := by
    intro a ha
    have ha' : a ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ha
    exact (norm_coordinate_le_graded F bond hi (f a)).trans (hbound a ha')
  simpa only [projectiveUnitIntegral_coordinate, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- Any Banach-valued coordinate functional commutes with the actual integral. -/
theorem projectiveUnitIntegral_coordinate_map
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : ℝ → ProjectiveLimit F bond} (hf : Continuous f) (n : ℕ)
    (L : F n →L[ℝ] G) :
    L ((projectiveUnitIntegral f hf).val n) =
      ∫ a in (0 : ℝ)..1, L ((f a).val n) := by
  exact (L.intervalIntegral_comp_comm
    (((projectiveCoordinate F bond n).continuous.comp hf).intervalIntegrable 0 1)).symm

section Multilinear

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {k : ℕ}

def projectiveUnitIntegralMultilinear
    (A : ℝ → E [×k]→L[ℝ] ProjectiveLimit F bond)
    (hA : Continuous (fun p : ℝ × (Fin k → E) => A p.1 p.2)) :
    E [×k]→L[ℝ] ProjectiveLimit F bond where
  toFun v := projectiveUnitIntegral (fun a => A a v)
    (hA.comp (continuous_id.prodMk continuous_const))
  map_update_add' v i x y := by
    have hx := hA.comp (continuous_id.prodMk (continuous_const (y := Function.update v i x)))
    have hy := hA.comp (continuous_id.prodMk (continuous_const (y := Function.update v i y)))
    exact (projectiveUnitIntegral_congr
      (hA.comp (continuous_id.prodMk continuous_const)) (hx.add hy)
      (fun a _ => (A a).map_update_add v i x y)).trans
        (projectiveUnitIntegral_add hx hy)
  map_update_smul' v i c x := by
    have hx := hA.comp (continuous_id.prodMk (continuous_const (y := Function.update v i x)))
    exact (projectiveUnitIntegral_congr
      (hA.comp (continuous_id.prodMk continuous_const)) (hx.const_smul c)
      (fun a _ => (A a).map_update_smul v i c x)).trans
        (projectiveUnitIntegral_smul hx c)
  cont := continuous_projectiveUnitIntegral
    (hA.comp (continuous_snd.prodMk continuous_fst))

theorem projectiveUnitIntegralMultilinear_apply
    (A : ℝ → E [×k]→L[ℝ] ProjectiveLimit F bond)
    (hA : Continuous (fun p : ℝ × (Fin k → E) => A p.1 p.2))
    (v : Fin k → E) :
    projectiveUnitIntegralMultilinear A hA v =
      projectiveUnitIntegral (fun a => A a v)
        (hA.comp (continuous_id.prodMk continuous_const)) := rfl

end Multilinear

/-- Joint continuity of a Banach-valued derivative supplies domination on
the compact parameter interval and a small compact interval in the variable. -/
theorem unitParameterIntegral_hasDerivAt
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {H H' : ℝ → ℝ → G}
    (hH : Continuous (fun p : ℝ × ℝ => H p.1 p.2))
    (hH' : Continuous (fun p : ℝ × ℝ => H' p.1 p.2))
    (hderiv : ∀ a t, HasDerivAt (H a) (H' a t) t) (t : ℝ) :
    HasDerivAt (fun x => ∫ a in (0 : ℝ)..1, H a x)
      (∫ a in (0 : ℝ)..1, H' a t) t := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (t - 1) (t + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hH'.continuousOn
  have hi : IntervalIntegrable (fun a => H a t) volume 0 1 :=
    (hH.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x a => H a x) (F' := fun x a => H' a x)
    (s := Ioo (t - 1) (t + 1)) (bound := fun _ => B)
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ hi ?_ ?_
    intervalIntegrable_const ?_).2
  · exact Eventually.of_forall fun x =>
      (hH.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (hH'.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun a ha x hx => hB (a, x)
      ⟨by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ha,
        ⟨hx.1.le, hx.2.le⟩⟩
  · exact Eventually.of_forall fun a _ x _ => hderiv a x

end ContinuousFlexibility.Analysis
