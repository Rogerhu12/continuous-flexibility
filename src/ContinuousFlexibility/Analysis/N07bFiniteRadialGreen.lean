import ContinuousFlexibility.Analysis.N07bFiniteInteriorGreen
import ContinuousFlexibility.Radial.ReferenceSmoothGreen

/-!
# The reference differential expression for finite-regularity heights

Reference reconstruction need not be infinitely differentiable across
physical interfaces. Its C² representative still has the actual radial
Jacobi expression and satisfies Green symmetry against compact radial
tests. The proof ignores the measure-zero radial endpoints explicitly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

/-- The slice and Fréchet definitions agree under local C² regularity. -/
theorem n07b_c2_radialPDE_eq_polar_jets
    {w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hw : DifferentiableAt ℝ w x.1) (hu : ContDiffAt ℝ 2 u x) :
    radialPDE w (fun r θ => u (r, θ)) x.1 x.2 =
      deriv w x.1 * radialPartial u x + w x.1 * radialPartial (radialPartial u) x +
        deriv w x.1 / x.1 * angularPartial (angularPartial u) x := by
  have hd : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y :=
    (hu.eventually (by norm_num)).mono (fun _ hy => hy.differentiableAt (by norm_num))
  have hrmap : Tendsto (fun r : ℝ => (r, x.2)) (𝓝 x.1) (𝓝 x) := by
    simpa only [ContinuousAt, id_eq, Prod.eta] using
      (continuousAt_id.prodMk continuousAt_const :
        ContinuousAt (fun r : ℝ => (r, x.2)) x.1)
  have hθmap : Tendsto (fun θ : ℝ => (x.1, θ)) (𝓝 x.2) (𝓝 x) := by
    simpa only [ContinuousAt, id_eq, Prod.eta] using
      (continuousAt_const.prodMk continuousAt_id :
        ContinuousAt (fun θ : ℝ => (x.1, θ)) x.2)
  have hrad : deriv (fun r => u (r, x.2)) =ᶠ[𝓝 x.1]
      (fun r => radialPartial u (r, x.2)) := by
    filter_upwards [hrmap.eventually hnear] with r hr
    exact (hasDerivAt_radialSlice (f := u) (x := (r, x.2)) hr).deriv
  have hang : deriv (fun θ => u (x.1, θ)) =ᶠ[𝓝 x.2]
      (fun θ => angularPartial u (x.1, θ)) := by
    filter_upwards [hθmap.eventually hnear] with θ hθ
    exact (hasDerivAt_angularSlice (f := u) (x := (x.1, θ)) hθ).deriv
  have hdr : DifferentiableAt ℝ (radialPartial u) x :=
    (contDiffAt_radialPartial hu (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdθ : DifferentiableAt ℝ (angularPartial u) x :=
    (contDiffAt_angularPartial hu (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hr₂ := (hasDerivAt_radialSlice hdr).congr_of_eventuallyEq hrad
  have hθ₂ := (hasDerivAt_angularSlice hdθ).congr_of_eventuallyEq hang
  have hf := hw.hasDerivAt.mul hr₂
  rw [(hasDerivAt_radialSlice hd).deriv] at hf
  change HasDerivAt (fun t => w t * deriv (fun r => u (r, x.2)) t)
    (deriv w x.1 * radialPartial u x + w x.1 * radialPartial (radialPartial u) x) x.1 at hf
  unfold radialPDE
  change deriv (fun t => w t * deriv (fun r => u (r, x.2)) t) x.1 +
    deriv w x.1 / x.1 * deriv (deriv (fun θ => u (x.1, θ))) x.2 = _
  rw [hf.deriv, hθ₂.deriv]

/-- The reference matrix is the actual radial differential expression at
every point with nonzero radius; only two height derivatives are used. -/
theorem n07b_c2_reference_divergence_eq_radialPDE
    {w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiffAt ℝ 2 u x) (hr : x.1 ≠ 0) :
    symmetricDivergence (radialHeightField w) (fun _ => 0)
      (radialHeightField (fun r => deriv w r / r)) u x =
        radialPDE w (fun r θ => u (r, θ)) x.1 x.2 := by
  have hwd := hw.differentiable (by simp) x.1
  have hq : DifferentiableAt ℝ (fun r => deriv w r / r) x.1 :=
    ((contDiff_infty_iff_deriv.mp hw).2.differentiable (by simp) x.1).div
      differentiableAt_id hr
  have hA : DifferentiableAt ℝ (radialHeightField w) x :=
    (contDiff_radialHeightField hw).differentiable (by simp) x
  have hC : DifferentiableAt ℝ
      (radialHeightField (fun r => deriv w r / r)) x :=
    hq.comp x differentiableAt_fst
  have hur : DifferentiableAt ℝ (radialPartial u) x :=
    (contDiffAt_radialPartial hu (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have huθ : DifferentiableAt ℝ (angularPartial u) x :=
    (contDiffAt_angularPartial hu (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [n07b_c2_radialPDE_eq_polar_jets hwd hu]
  have hN : symmetricNormalFlux (radialHeightField w) (fun _ => 0) u =
      (fun y => radialHeightField w y * radialPartial u y) := by
    funext y
    simp only [symmetricNormalFlux, zero_mul, add_zero]
  have hT : symmetricAngularFlux (fun _ => 0)
      (radialHeightField (fun r => deriv w r / r)) u =
      (fun y => radialHeightField (fun r => deriv w r / r) y * angularPartial u y) := by
    funext y
    simp only [symmetricAngularFlux, zero_mul, zero_add]
  rw [symmetricDivergence, hN, hT, radialPartial_mul hA hur, angularPartial_mul hC huθ,
    radialPartial_radialHeightField hwd, angularPartial_radialHeightField hq]
  simp only [radialHeightField, zero_mul, zero_add]

/-- The actual reference weak pairing equals the classical expression
against a compact radial test for any interior C² periodic height. -/
theorem n07b_c2_reference_green {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u φ : PolarPoint → ℝ}
    (hu : ContDiffOn ℝ 2 u (annularOpen D))
    (hup : Function.Periodic u (0, Real.pi)) (hφ : RadialTest D φ) :
    radialWeakPairing D u φ =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        radialPDE D.w (fun s α => u (s, α)) r θ * φ (r, θ)) := by
  let L : SymmetricCoefficients :=
    ⟨radialHeightField D.w, fun _ => 0,
      radialHeightField (fun r => deriv D.w r / r)⟩
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hw := hgeom.2.2.1.1
  have hr : ∀ p ∈ annularOpen D, p.1 ≠ 0 :=
    fun p hp => (hgeom.1.trans hp.1.1).ne'
  have ha : ContDiffOn ℝ 1 L.a (annularOpen D) :=
    ((contDiff_radialHeightField hw).of_le (by simp)).contDiffOn
  have hb : ContDiffOn ℝ 1 L.b (annularOpen D) := contDiffOn_const
  have hc : ContDiffOn ℝ 1 L.c (annularOpen D) := by
    intro p hp
    have hq : ContDiffAt ℝ ∞ (fun r => deriv D.w r / r) p.1 :=
      (contDiff_infty_iff_deriv.mp hw).2.contDiffAt.div contDiffAt_id (hr p hp)
    exact ((hq.comp p contDiffAt_fst).of_le (by simp)).contDiffWithinAt
  have hg := n07b_c2_interior_physical_green_of_pi_periodic hgeom.2.1
    ha hb hc hu (fun _ _ _ => rfl) (fun _ _ _ => rfl) hup hφ
  have hident (v : PolarPoint → ℝ) {p : PolarPoint}
      (hp : p ∈ annularOpen D) (hv : ContDiffAt ℝ 2 v p) :
      divergenceOperator L v p = radialPDE D.w (fun r θ => v (r, θ)) p.1 p.2 :=
    n07b_c2_reference_divergence_eq_radialPDE hw hv (hr p hp)
  calc
    radialWeakPairing D u φ =
        ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          u (r, θ) * divergenceOperator L φ (r, θ)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hgeom.2.1.le
      intro r hr'
      apply congrArg radialAngularMean
      funext θ
      rw [hident φ ⟨hr', mem_univ _⟩ (hφ.1.contDiffAt.of_le (by simp))]
    _ = ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          divergenceOperator L u (r, θ) * φ (r, θ)) := hg
    _ = _ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hgeom.2.1.le
      intro r hr'
      apply congrArg radialAngularMean
      funext θ
      rw [hident u ⟨hr', mem_univ _⟩
        ((hu (r, θ) ⟨hr', mem_univ _⟩).contDiffAt (hopen.mem_nhds ⟨hr', mem_univ _⟩))]

end ContinuousFlexibility.Analysis

