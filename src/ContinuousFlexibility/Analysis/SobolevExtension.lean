module

public import ContinuousFlexibility.Analysis.IntervalSobolevExtension

/-!
# Universal extension on half-lines and intervals

This is the extension-operator assertion in the external-input appendix.
The Sobolev indices are all nonnegative integers, as in the manuscript's
grading. Norms are the actual derivative `L²` norms; the Sobolev spaces are
their completions on functions smooth up to the boundary.

One linear map on smooth functions is constructed for each domain. Its
bounded extensions to every Sobolev completion are compatible, retain the
input on the domain, and are genuine right inverses of restriction. Neither
an extension theorem nor a family of order-dependent extension operators is
assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A single linear extension with a bound in every derivative Sobolev norm. -/
structure SobolevExtensionOperator (s : Set ℝ) (hs : MeasurableSet s)
    (hu : UniqueDiffOn ℝ s) where
  core : smoothSobolevCore F s hs hu →ₗ[ℝ] LineSobolevCore F
  bound : ℕ → ℝ
  bound_nonneg : ∀ k, 0 ≤ bound k
  norm_bound : ∀ k (f : smoothSobolevCore F s hs hu),
    ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k (core f)‖ ≤
      bound k * ‖sobolevCoreJet F s hs hu k f‖
  retains : ∀ (f : smoothSobolevCore F s hs hu) (x : ℝ), x ∈ s → core f x = f x

namespace SobolevExtensionOperator

variable {F} {s : Set ℝ} {hs : MeasurableSet s} {hu : UniqueDiffOn ℝ s}

def completion (E : SobolevExtensionOperator F s hs hu) (k : ℕ) :
    SobolevJetCompletion F s hs hu k →L[ℝ]
      SobolevJetCompletion F univ MeasurableSet.univ uniqueDiffOn_univ k :=
  sobolevJetExtension F E.core k

theorem completion_norm_le (E : SobolevExtensionOperator F s hs hu) (k : ℕ) :
    ‖E.completion k‖ ≤ E.bound k :=
  norm_sobolevJetExtension_le F E.core k (E.bound_nonneg k) (E.norm_bound k)

theorem completion_apply_core (E : SobolevExtensionOperator F s hs hu)
    (k : ℕ) (f : smoothSobolevCore F s hs hu) :
    E.completion k (coreToSobolevJet F s hs hu k f) =
      coreToSobolevJet F univ MeasurableSet.univ uniqueDiffOn_univ k (E.core f) :=
  sobolevJetExtension_apply F E.core k (E.norm_bound k) f

/-- Restricting the completed extension gives the original Sobolev element. -/
theorem completion_rightInverse (E : SobolevExtensionOperator F s hs hu) (k : ℕ) :
    (sobolevRestriction F s hs hu k).comp (E.completion k) =
      ContinuousLinearMap.id ℝ (SobolevJetCompletion F s hs hu k) :=
  sobolevRestriction_comp_extension F s hs hu E.core k (E.norm_bound k) E.retains

theorem completion_compatible (E : SobolevExtensionOperator F s hs hu)
    {k m : ℕ} (hkm : k ≤ m) :
    (sobolevJetBonding F univ MeasurableSet.univ uniqueDiffOn_univ hkm).comp (E.completion m) =
      (E.completion k).comp (sobolevJetBonding F s hs hu hkm) :=
  sobolevJetExtension_compatible F E.core hkm (E.norm_bound k) (E.norm_bound m)

/-- Transport one extension by an affine orientation. This single lemma
handles both ends of an interval and both half-lines. -/
def affine {t : Set ℝ} (E : SobolevExtensionOperator F s hs hu)
    (ht : MeasurableSet t) (hv : UniqueDiffOn ℝ t)
    (a c : ℝ) (hc : c = 1 ∨ c = -1)
    (hst : s = (fun x : ℝ => a + c * x) ⁻¹' t) :
    SobolevExtensionOperator F t ht hv where
  core := sobolevCoreAffineExtension hs ht hu hv a c hc hst E.core
  bound := E.bound
  bound_nonneg := E.bound_nonneg
  norm_bound k := sobolevCoreAffineExtension_bound hs ht hu hv a c hc hst E.core k
    (E.bound k) (E.norm_bound k)
  retains f x hx := sobolevCoreAffineExtension_rightInverse hs ht hu hv a c hc hst E.core
    (fun g y hy => E.retains g y hy) f hx

end SobolevExtensionOperator

/-- A fully constructed extension from `[0,∞)`, with no analytic input
assumed about the existence of extension operators. -/
def halfLineSobolevExtensionZero :
    SobolevExtensionOperator F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) where
  core := seeleySobolevCoreExtension seeleyData
  bound := seeleySobolevBound seeleyData
  bound_nonneg := seeleySobolevBound_nonneg seeleyData
  norm_bound := seeleySobolevCoreExtension_bound seeleyData
  retains f _ hx := seeleySobolevCoreExtension_rightInverse seeleyData f hx

/-- `right = true` gives `[a,∞)` and `right = false` gives `(-∞,a]`. -/
def orientedHalfLine (a : ℝ) (right : Bool) : Set ℝ :=
  if right then Ici a else Iic a

theorem measurableSet_orientedHalfLine (a : ℝ) (right : Bool) :
    MeasurableSet (orientedHalfLine a right) := by
  cases right with
  | false => exact measurableSet_Iic
  | true => exact measurableSet_Ici

theorem uniqueDiffOn_orientedHalfLine (a : ℝ) (right : Bool) :
    UniqueDiffOn ℝ (orientedHalfLine a right) := by
  cases right with
  | false => exact uniqueDiffOn_Iic a
  | true => exact uniqueDiffOn_Ici a

private def halfLineOrientation (right : Bool) : ℝ := if right then 1 else -1

private theorem halfLineOrientation_unit (right : Bool) :
    halfLineOrientation right = 1 ∨ halfLineOrientation right = -1 := by
  cases right <;> simp [halfLineOrientation]

private theorem halfLineOrientation_preimage (a : ℝ) (right : Bool) :
    Ici (0 : ℝ) = (fun x : ℝ => a + halfLineOrientation right * x) ⁻¹'
      orientedHalfLine a right := by
  ext x
  cases right <;> simp [orientedHalfLine, halfLineOrientation]

/-- The universal extension on either half-line, with any finite endpoint. -/
def halfLineSobolevExtension (a : ℝ) (right : Bool) :
    SobolevExtensionOperator F (orientedHalfLine a right)
      (measurableSet_orientedHalfLine a right) (uniqueDiffOn_orientedHalfLine a right) :=
  (halfLineSobolevExtensionZero F).affine (measurableSet_orientedHalfLine a right)
    (uniqueDiffOn_orientedHalfLine a right) a (halfLineOrientation right)
    (halfLineOrientation_unit right) (halfLineOrientation_preimage a right)

theorem exists_halfLineSobolevExtension (a : ℝ) (right : Bool) :
    Nonempty (SobolevExtensionOperator F (orientedHalfLine a right)
      (measurableSet_orientedHalfLine a right) (uniqueDiffOn_orientedHalfLine a right)) :=
  ⟨halfLineSobolevExtension F a right⟩

def intervalSobolevExtensionZero (L : ℝ) (hL : 0 < L) :
    SobolevExtensionOperator F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) where
  core := intervalSeeleyCoreExtension seeleyData L hL
  bound := intervalSeeleySobolevBound seeleyData L hL
  bound_nonneg := intervalSeeleySobolevBound_nonneg seeleyData L hL
  norm_bound := intervalSeeleyCoreExtension_bound seeleyData L hL
  retains f _ hx := intervalSeeleyCoreExtension_rightInverse seeleyData L hL f hx

private theorem interval_translation_preimage (a b : ℝ) :
    Icc (0 : ℝ) (b - a) = (fun x : ℝ => a + (1 : ℝ) * x) ⁻¹' Icc a b := by
  ext x
  simp only [mem_preimage, mem_Icc, one_mul]
  constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith

/-- The universal extension on any nondegenerate finite interval. -/
def intervalSobolevExtension (a b : ℝ) (hab : a < b) :
    SobolevExtensionOperator F (Icc a b) measurableSet_Icc (uniqueDiffOn_Icc hab) :=
  (intervalSobolevExtensionZero F (b - a) (sub_pos.mpr hab)).affine
    measurableSet_Icc (uniqueDiffOn_Icc hab) a 1 (Or.inl rfl)
    (interval_translation_preimage a b)

theorem exists_intervalSobolevExtension (a b : ℝ) (hab : a < b) :
    Nonempty (SobolevExtensionOperator F (Icc a b) measurableSet_Icc (uniqueDiffOn_Icc hab)) :=
  ⟨intervalSobolevExtension F a b hab⟩

end ContinuousFlexibility.Analysis
