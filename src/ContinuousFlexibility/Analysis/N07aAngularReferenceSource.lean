import ContinuousFlexibility.Analysis.N07aCoefficientSymmetry
import ContinuousFlexibility.Radial.RadialHeight
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The actual measurable reference differential source

The polar differential expression is Borel even for a merely C¹ global
field: totalized Fréchet derivatives are measurable. Setting its value to
zero on the interfaces changes no physical or canonical L² class. The
angular period and evenness follow from the actual derivative symmetries.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open Filter
open scoped Topology ContDiff

theorem n07a_referenceField_measurable {D : ReferenceData} {v : PolarPoint → ℝ}
    (hv : ContinuousOn v (annularOpen D))
    (hzero : ∀ p, p ∉ annularOpen D → v p = 0) : Measurable v := by
  classical
  have h : Measurable ((annularOpen D).piecewise v (fun _ => (0 : ℝ))) :=
    hv.measurable_piecewise continuousOn_const (isOpen_Ioo.prod isOpen_univ).measurableSet
  have he : (annularOpen D).piecewise v (fun _ => (0 : ℝ)) = v := by
    funext p
    by_cases hp : p ∈ annularOpen D
    · exact piecewise_eq_of_mem (annularOpen D) v (fun _ => (0 : ℝ)) hp
    · exact (piecewise_eq_of_notMem (annularOpen D) v (fun _ => (0 : ℝ)) hp).trans
        (hzero p hp).symm
  exact he ▸ h

def n07aReferenceDifferential (D : ReferenceData) (v : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  deriv D.w p.1 * radialPartial v p + D.w p.1 * radialPartial (radialPartial v) p +
    deriv D.w p.1 / p.1 * angularPartial (angularPartial v) p

def n07aReferencePieceInterior {S : PhysicalSpacesData} (K : CanonicalData S) : Set PolarPoint :=
  ⋃ m, referencePhysicalPieceOpen S K m

def n07aReferenceInteriorDifferential {S : PhysicalSpacesData} (D : ReferenceData)
    (K : CanonicalData S) (v : PolarPoint → ℝ) : PolarPoint → ℝ :=
  (n07aReferencePieceInterior K).indicator (n07aReferenceDifferential D v)

/-- The actual reference expression only needs smoothness near the point.
In particular this applies on an open physical piece, even when the
global reference realization is only C¹ across its boundary. -/
theorem n07a_referenceDifferential_eq_radialPDE {D : ReferenceData}
    {v : PolarPoint → ℝ} {p : PolarPoint}
    (hw : DifferentiableAt ℝ D.w p.1) (hv : ContDiffAt ℝ ∞ v p) :
    n07aReferenceDifferential D v p =
      Radial.radialPDE D.w (fun r θ => v (r, θ)) p.1 p.2 := by
  have hv1 : ContDiffAt ℝ 1 v p := hv.of_le (by simp)
  have hd : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ v q :=
    (hv1.eventually (by simp)).mono fun _ hq => hq.differentiableAt one_ne_zero
  have hrad : (fun r => deriv (fun t => v (t, p.2)) r) =ᶠ[𝓝 p.1]
      (fun r => radialPartial v (r, p.2)) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hd] with r hr
    exact (Radial.hasDerivAt_radialSlice hr).deriv
  have hang : (fun θ => deriv (fun t => v (p.1, t)) θ) =ᶠ[𝓝 p.2]
      (fun θ => angularPartial v (p.1, θ)) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hd] with θ hθ
    exact (Radial.hasDerivAt_angularSlice hθ).deriv
  have hr₂ := Radial.hasDerivAt_radialSlice
    ((contDiffAt_radialPartial hv (m := 1) (by simp)).differentiableAt one_ne_zero)
  have ht₂ := Radial.hasDerivAt_angularSlice
    ((contDiffAt_angularPartial hv (m := 1) (by simp)).differentiableAt one_ne_zero)
  have hrd := hr₂.congr_of_eventuallyEq hrad
  have htd := ht₂.congr_of_eventuallyEq hang
  have hf := hw.hasDerivAt.mul hrd
  rw [(Radial.hasDerivAt_radialSlice (hv.differentiableAt (by simp))).deriv] at hf
  change _ = deriv (fun r => D.w r * deriv (fun t => v (t, p.2)) r) p.1 +
    deriv D.w p.1 / p.1 * deriv (deriv (fun θ => v (p.1, θ))) p.2
  have hf' : deriv (fun r => D.w r * deriv (fun t => v (t, p.2)) r) p.1 =
      deriv D.w p.1 * radialPartial v p + D.w p.1 * radialPartial (radialPartial v) p := by
    have he : (D.w * fun r => deriv (fun t => v (t, p.2)) r) =
        (fun r => D.w r * deriv (fun t => v (t, p.2)) r) := by
      funext r
      exact Pi.mul_apply _ _ _
    exact (congrArg (fun f : ℝ → ℝ => deriv f p.1) he.symm).trans hf.deriv
  rw [hf', htd.deriv]
  rfl

theorem n07aReferencePieceInterior_isOpen {S : PhysicalSpacesData} (K : CanonicalData S) :
    IsOpen (n07aReferencePieceInterior K) :=
  isOpen_iUnion fun _ => isOpen_Ioo.prod isOpen_univ

theorem n07aReferenceDifferential_measurable {D : ReferenceData}
    (hw : Measurable D.w) (v : PolarPoint → ℝ) :
    Measurable (n07aReferenceDifferential D v) := by
  have hr : Measurable (radialPartial v) := measurable_fderiv_apply_const ℝ v (1, 0)
  have hrr : Measurable (radialPartial (radialPartial v)) :=
    measurable_fderiv_apply_const ℝ (radialPartial v) (1, 0)
  have htt : Measurable (angularPartial (angularPartial v)) :=
    measurable_fderiv_apply_const ℝ (angularPartial v) (0, 1)
  exact (((measurable_deriv D.w).comp measurable_fst).mul hr |>.add
    ((hw.comp measurable_fst).mul hrr)).add
      ((((measurable_deriv D.w).comp measurable_fst).div measurable_fst).mul htt)

theorem n07aReferenceInteriorDifferential_measurable {D : ReferenceData}
    {S : PhysicalSpacesData} (K : CanonicalData S) (hw : Measurable D.w) (v : PolarPoint → ℝ) :
    Measurable (n07aReferenceInteriorDifferential D K v) :=
  (n07aReferenceDifferential_measurable hw v).indicator
    (n07aReferencePieceInterior_isOpen K).measurableSet

theorem n07aReferenceInteriorDifferential_on_piece {D : ReferenceData}
    {S : PhysicalSpacesData} {K : CanonicalData S} (v : PolarPoint → ℝ)
    {m : ℕ} {p : PolarPoint} (hp : p ∈ referencePhysicalPieceOpen S K m) :
    n07aReferenceInteriorDifferential D K v p = n07aReferenceDifferential D v p :=
  indicator_of_mem (mem_iUnion.mpr ⟨m, hp⟩) _

theorem n07aReferenceDifferential_periodic (D : ReferenceData) {v : PolarPoint → ℝ}
    (hv : Function.Periodic v (0, Real.pi)) :
    Function.Periodic (n07aReferenceDifferential D v) (0, Real.pi) := by
  intro p
  simp only [n07aReferenceDifferential, Prod.fst_add, add_zero,
    periodic_radialPartial hv p, periodic_radialPartial (periodic_radialPartial hv) p,
    periodic_angularPartial (periodic_angularPartial hv) p]

theorem n07aReferenceDifferential_even (D : ReferenceData) {v : PolarPoint → ℝ}
    (hv : ∀ r θ, v (r, -θ) = v (r, θ)) :
    ∀ r θ, n07aReferenceDifferential D v (r, -θ) = n07aReferenceDifferential D v (r, θ) := by
  have hr : ∀ r θ, radialPartial v (r, -θ) = radialPartial v (r, θ) := by
    intro r θ
    simpa only [one_mul] using (n07a_coordinatePartials_reflection
      (σ := 1) (by simpa only [one_mul] using hv) r θ).1
  have hrr : ∀ r θ, radialPartial (radialPartial v) (r, -θ) = radialPartial (radialPartial v) (r, θ) := by
    intro r θ
    simpa only [one_mul] using (n07a_coordinatePartials_reflection
      (σ := 1) (by simpa only [one_mul] using hr) r θ).1
  have ht : ∀ r θ, angularPartial v (r, -θ) = -angularPartial v (r, θ) := by
    intro r θ
    simpa only [neg_one_mul] using (n07a_coordinatePartials_reflection
      (σ := 1) (by simpa only [one_mul] using hv) r θ).2
  have htt : ∀ r θ, angularPartial (angularPartial v) (r, -θ) = angularPartial (angularPartial v) (r, θ) := by
    intro r θ
    simpa only [neg_neg, one_mul] using (n07a_coordinatePartials_reflection
      (σ := -1) (by simpa only [neg_one_mul] using ht) r θ).2
  intro r θ
  simp only [n07aReferenceDifferential, hr, hrr, htt]

theorem n07aReferenceInteriorDifferential_periodic {S : PhysicalSpacesData}
    (D : ReferenceData) (K : CanonicalData S) {v : PolarPoint → ℝ}
    (hv : Function.Periodic v (0, Real.pi)) :
    Function.Periodic (n07aReferenceInteriorDifferential D K v) (0, Real.pi) := by
  intro p
  have hmem : p + (0, Real.pi) ∈ n07aReferencePieceInterior K ↔ p ∈ n07aReferencePieceInterior K := by
    simp only [n07aReferencePieceInterior, mem_iUnion, referencePhysicalPieceOpen,
      mem_prod, Prod.fst_add, add_zero, mem_univ, and_true]
  by_cases hp : p ∈ n07aReferencePieceInterior K
  · simp only [n07aReferenceInteriorDifferential, indicator_of_mem hp,
      indicator_of_mem (hmem.mpr hp), n07aReferenceDifferential_periodic D hv p]
  · simp only [n07aReferenceInteriorDifferential, indicator_of_notMem hp,
      indicator_of_notMem (mt hmem.mp hp)]

theorem n07aReferenceInteriorDifferential_even {S : PhysicalSpacesData}
    (D : ReferenceData) (K : CanonicalData S) {v : PolarPoint → ℝ}
    (hv : ∀ r θ, v (r, -θ) = v (r, θ)) :
    ∀ r θ, n07aReferenceInteriorDifferential D K v (r, -θ) =
      n07aReferenceInteriorDifferential D K v (r, θ) := by
  intro r θ
  have hmem : (r, -θ) ∈ n07aReferencePieceInterior K ↔ (r, θ) ∈ n07aReferencePieceInterior K := by
    simp only [n07aReferencePieceInterior, mem_iUnion, referencePhysicalPieceOpen, mem_prod, mem_univ, and_true]
  by_cases hp : (r, θ) ∈ n07aReferencePieceInterior K
  · simp only [n07aReferenceInteriorDifferential, indicator_of_mem hp,
      indicator_of_mem (hmem.mpr hp), n07aReferenceDifferential_even D hv r θ]
  · simp only [n07aReferenceInteriorDifferential, indicator_of_notMem hp,
      indicator_of_notMem (mt hmem.mp hp)]

end ContinuousFlexibility.Analysis
