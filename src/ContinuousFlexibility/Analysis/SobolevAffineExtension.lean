module

public import ContinuousFlexibility.Analysis.SobolevAffineTransport
public import ContinuousFlexibility.Analysis.SobolevJetCompletion
public import Mathlib.Tactic.Ring

/-!
# Transport of one common Sobolev extension by an affine orientation

Translations and reflections preserve every actual derivative L² norm and
therefore the finite Sobolev jet norm. Conjugating one smooth-core extension
by an affine orientation gives a linear extension on the transported domain,
with the same bound at every Sobolev order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- An affine orientation preserves the full, actual derivative Sobolev norm. -/
theorem norm_sobolevCoreJet_affine {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (k : ℕ) (f : smoothSobolevCore F t ht hut) :
    ‖sobolevCoreJet F s hs hus k
        (smoothSobolevAffinePullback hs ht hus hut a c hc hst f)‖ =
      ‖sobolevCoreJet F t ht hut k f‖ := by
  have hfun : (smoothSobolevAffinePullback hs ht hus hut a c hc hst f : ℝ → F) =
      fun x => f (a + c * x) := by
    funext x
    exact smoothSobolevAffinePullback_apply hs ht hus hut a c hc hst f x
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sobolevCoreJet_sq, norm_sobolevCoreJet_sq]
  apply Finset.sum_congr rfl
  intro j _
  rw [hfun, eLpNorm_iteratedDerivWithin_affine hs ht hus hut a c hc hst f j.val]

theorem affine_orientation_inverse (a c : ℝ) (hc : c = 1 ∨ c = -1) (x : ℝ) :
    a + c * (-c * a + c * x) = x := by
  rcases hc with rfl | rfl <;> ring

/-- Pull back to the standard domain, apply its fixed extension, and pull
back by the inverse affine map on the whole line. This is one genuine linear
map on smooth functions, independent of any Sobolev order. -/
def sobolevCoreAffineExtension {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (E : smoothSobolevCore F s hs hus →ₗ[ℝ] LineSobolevCore F) :
    smoothSobolevCore F t ht hut →ₗ[ℝ] LineSobolevCore F :=
  (smoothSobolevAffinePullback MeasurableSet.univ MeasurableSet.univ
      uniqueDiffOn_univ uniqueDiffOn_univ (-c * a) c hc (by simp)).comp
    (E.comp (smoothSobolevAffinePullback hs ht hus hut a c hc hst))

@[simp] theorem sobolevCoreAffineExtension_apply {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (E : smoothSobolevCore F s hs hus →ₗ[ℝ] LineSobolevCore F)
    (f : smoothSobolevCore F t ht hut) (x : ℝ) :
    sobolevCoreAffineExtension hs ht hus hut a c hc hst E f x =
      E (smoothSobolevAffinePullback hs ht hus hut a c hc hst f) (-c * a + c * x) := by
  simp only [sobolevCoreAffineExtension, LinearMap.comp_apply,
    smoothSobolevAffinePullback_apply]

/-- Pointwise extension on the standard domain transports to pointwise
extension on the target domain, including its boundary. -/
theorem sobolevCoreAffineExtension_rightInverse {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (E : smoothSobolevCore F s hs hus →ₗ[ℝ] LineSobolevCore F)
    (hE : ∀ g : smoothSobolevCore F s hs hus, EqOn (E g) g s)
    (f : smoothSobolevCore F t ht hut) {x : ℝ} (hx : x ∈ t) :
    sobolevCoreAffineExtension hs ht hus hut a c hc hst E f x = f x := by
  have hi : a + c * (-c * a + c * x) = x := affine_orientation_inverse a c hc x
  have hsx : -c * a + c * x ∈ s := by
    rw [hst]
    simpa only [mem_preimage, hi] using hx
  calc
    sobolevCoreAffineExtension hs ht hus hut a c hc hst E f x =
        E (smoothSobolevAffinePullback hs ht hus hut a c hc hst f)
          (-c * a + c * x) :=
      sobolevCoreAffineExtension_apply hs ht hus hut a c hc hst E f x
    _ = smoothSobolevAffinePullback hs ht hus hut a c hc hst f (-c * a + c * x) :=
      hE _ hsx
    _ = f (a + c * (-c * a + c * x)) :=
      smoothSobolevAffinePullback_apply hs ht hus hut a c hc hst f _
    _ = f x := congrArg f hi

/-- The transported extension has exactly the same Sobolev bound as the
original one, with no loss from either change of coordinates. -/
theorem sobolevCoreAffineExtension_bound {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (E : smoothSobolevCore F s hs hus →ₗ[ℝ] LineSobolevCore F)
    (k : ℕ) (C : ℝ)
    (hE : ∀ g, ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k (E g)‖ ≤
      C * ‖sobolevCoreJet F s hs hus k g‖)
    (f : smoothSobolevCore F t ht hut) :
    ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k
        (sobolevCoreAffineExtension hs ht hus hut a c hc hst E f)‖ ≤
      C * ‖sobolevCoreJet F t ht hut k f‖ := by
  calc
    _ = ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k
        (E (smoothSobolevAffinePullback hs ht hus hut a c hc hst f))‖ := by
      simpa only [sobolevCoreAffineExtension, LinearMap.comp_apply] using
        norm_sobolevCoreJet_affine MeasurableSet.univ MeasurableSet.univ
          uniqueDiffOn_univ uniqueDiffOn_univ (-c * a) c hc (by simp) k
          (E (smoothSobolevAffinePullback hs ht hus hut a c hc hst f))
    _ ≤ C * ‖sobolevCoreJet F s hs hus k
        (smoothSobolevAffinePullback hs ht hus hut a c hc hst f)‖ := hE _
    _ = C * ‖sobolevCoreJet F t ht hut k f‖ := by
      rw [norm_sobolevCoreJet_affine hs ht hus hut a c hc hst]

/-- The same constant also bounds the transported operator on the completed
Sobolev spaces. -/
theorem norm_sobolevJetAffineExtension_le {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t)
    (E : smoothSobolevCore F s hs hus →ₗ[ℝ] LineSobolevCore F)
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ g, ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k (E g)‖ ≤
      C * ‖sobolevCoreJet F s hs hus k g‖) :
    ‖sobolevJetExtension F (sobolevCoreAffineExtension hs ht hus hut a c hc hst E) k‖ ≤ C :=
  norm_sobolevJetExtension_le F _ k hC
    (sobolevCoreAffineExtension_bound hs ht hus hut a c hc hst E k C hE)

end ContinuousFlexibility.Analysis
