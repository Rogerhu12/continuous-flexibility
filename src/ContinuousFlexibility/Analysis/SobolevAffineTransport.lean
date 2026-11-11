import ContinuousFlexibility.Analysis.SmoothSobolevCore
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# A common transport lemma for the two orientations of an interval

Translation and reflection preserve the actual derivative Sobolev norms.
The affine chain rule is proved once, for arbitrary source and target sets;
the measure-preserving case then covers either endpoint without duplicating
the extension argument.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Affine pullback of actual within-derivatives, with both domains explicit. -/
theorem iteratedDerivWithin_affine {s t : Set ℝ} {f : ℝ → F}
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hf : ContDiffOn ℝ ∞ f t) (a c : ℝ)
    (hmap : MapsTo (fun x => a + c * x) s t) (n : ℕ) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n (fun y => f (a + c * y)) s x =
      c ^ n • iteratedDerivWithin n f t (a + c * x) := by
  induction n generalizing x with
  | zero => simp only [iteratedDerivWithin_zero, pow_zero, one_smul]
  | succ n ih =>
    have he : EqOn (iteratedDerivWithin n (fun y => f (a + c * y)) s)
        (fun y => c ^ n • iteratedDerivWithin n f t (a + c * y)) s :=
      fun y hy => ih hy
    have hd : HasDerivWithinAt (iteratedDerivWithin n f t)
        (iteratedDerivWithin (n + 1) f t (a + c * x)) t (a + c * x) := by
      simpa only [iteratedDerivWithin_succ] using
        (hf.differentiableOn_iteratedDerivWithin (m := n) (by simp) ht _ (hmap hx)).hasDerivWithinAt
    have ha : HasDerivWithinAt (fun y : ℝ => a + c * y) c s x := by
      simpa only [mul_one] using
        (((hasDerivAt_id x).const_mul c).const_add a).hasDerivWithinAt
    rw [iteratedDerivWithin_succ, derivWithin_congr he (ih hx)]
    have hcomp := ((hd.scomp x ha hmap).const_smul (c ^ n)).derivWithin (hs x hx)
    simpa only [Pi.smul_def, Function.comp_def, smul_smul, pow_succ] using hcomp

/-- Both orientations preserve Lebesgue measure. -/
theorem measurePreserving_affine_orientation (a c : ℝ) (hc : c = 1 ∨ c = -1) :
    MeasurePreserving (fun x : ℝ => a + c * x) volume volume := by
  rcases hc with rfl | rfl
  · simpa only [one_mul] using measurePreserving_add_left (volume : Measure ℝ) a
  · simpa only [Function.comp_def, neg_one_mul] using
      (measurePreserving_add_left (volume : Measure ℝ) a).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem measurePreserving_affine_orientation_restrict {s t : Set ℝ}
    (ht : MeasurableSet t) (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t) :
    MeasurePreserving (fun x : ℝ => a + c * x) (volume.restrict s) (volume.restrict t) := by
  rw [hst]
  exact (measurePreserving_affine_orientation a c hc).restrict_preimage ht

/-- Smoothness and membership in every actual `L²` derivative space are
preserved by either affine orientation of the domain. -/
theorem smoothSobolevCore_affine_mem {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (f : smoothSobolevCore F t ht hut) :
    (fun x => f (a + c * x)) ∈ smoothSobolevCore F s hs hus := by
  have hmap : MapsTo (fun x : ℝ => a + c * x) s t := by
    intro x hx
    rwa [hst] at hx
  have hmeasure := measurePreserving_affine_orientation_restrict ht a c hc hst
  refine ⟨f.property.1.comp (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn hmap,
    fun n => ?_⟩
  have hp : MemLp ((iteratedDerivWithin n (f : ℝ → F) t) ∘ (fun x => a + c * x))
      2 (volume.restrict s) := (f.property.2 n).comp_measurePreserving hmeasure
  have he : (c ^ n • ((iteratedDerivWithin n (f : ℝ → F) t) ∘ (fun x => a + c * x)))
      =ᵐ[volume.restrict s] iteratedDerivWithin n (fun x => f (a + c * x)) s := by
    filter_upwards [ae_restrict_mem hs] with x hx
    exact (iteratedDerivWithin_affine hus hut f.property.1 a c hmap n hx).symm
  exact (memLp_congr_ae he).mp (hp.const_smul (c ^ n))

/-- The same affine pullback is a linear map on the actual smooth cores. -/
def smoothSobolevAffinePullback {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t) :
    smoothSobolevCore F t ht hut →ₗ[ℝ] smoothSobolevCore F s hs hus where
  toFun f := ⟨fun x => f (a + c * x), smoothSobolevCore_affine_mem hs ht hus hut a c hc hst f⟩
  map_add' f g := by ext x; simp only [Submodule.coe_add, Pi.add_apply]
  map_smul' r f := by ext x; simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem smoothSobolevAffinePullback_apply {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (f : smoothSobolevCore F t ht hut) (x : ℝ) :
    smoothSobolevAffinePullback hs ht hus hut a c hc hst f x = f (a + c * x) := rfl

/-- Exact invariance of each derivative `L²` norm under either orientation. -/
theorem eLpNorm_iteratedDerivWithin_affine {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (f : smoothSobolevCore F t ht hut) (n : ℕ) :
    eLpNorm (iteratedDerivWithin n (fun x => f (a + c * x)) s) 2 (volume.restrict s) =
      eLpNorm (iteratedDerivWithin n (f : ℝ → F) t) 2 (volume.restrict t) := by
  have hmap : MapsTo (fun x : ℝ => a + c * x) s t := by
    intro x hx
    rwa [hst] at hx
  have he : iteratedDerivWithin n (fun x => f (a + c * x)) s
      =ᵐ[volume.restrict s]
        c ^ n • ((iteratedDerivWithin n (f : ℝ → F) t) ∘ (fun x => a + c * x)) := by
    filter_upwards [ae_restrict_mem hs] with x hx
    exact iteratedDerivWithin_affine hus hut f.property.1 a c hmap n hx
  rw [eLpNorm_congr_ae he, eLpNorm_const_smul]
  have hn : ‖c ^ n‖ₑ = 1 := by
    rcases hc with rfl | rfl <;> simp
  rw [hn, one_mul]
  exact eLpNorm_comp_measurePreserving (f.property.2 n).aestronglyMeasurable
    (measurePreserving_affine_orientation_restrict ht a c hc hst)

end ContinuousFlexibility.Analysis
