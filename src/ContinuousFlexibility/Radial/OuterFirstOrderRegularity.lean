import ContinuousFlexibility.Radial.OuterFirstOrderState
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Regularity of the actual outer value/flux system

Smooth coefficients bootstrap the actual component derivatives to every
finite order.  The physical system also recovers the original Jacobi
equation directly from its genuine conormal flux.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology

theorem OuterFirstOrderSystem.continuousOn {alpha beta u z : ℝ → ℝ} {s : Set ℝ}
    (h : OuterFirstOrderSystem alpha beta u z s) :
    ContinuousOn u s ∧ ContinuousOn z s :=
  ⟨fun x hx => (h x hx).1.continuousAt.continuousWithinAt,
    fun x hx => (h x hx).2.continuousAt.continuousWithinAt⟩

theorem OuterFirstOrderSystem.continuousOn_deriv {alpha beta u z : ℝ → ℝ} {s : Set ℝ}
    (h : OuterFirstOrderSystem alpha beta u z s)
    (halpha : ContinuousOn alpha s) (hbeta : ContinuousOn beta s) :
    ContinuousOn (deriv u) s ∧ ContinuousOn (deriv z) s :=
  ⟨(halpha.mul h.continuousOn.2).congr (fun x hx => (h x hx).1.deriv),
    (hbeta.mul h.continuousOn.1).congr (fun x hx => (h x hx).2.deriv)⟩

/-- Every actual first-order state is smooth wherever its coefficients are smooth. -/
theorem OuterFirstOrderSystem.contDiffOn {alpha beta u z : ℝ → ℝ} {s : Set ℝ}
    (h : OuterFirstOrderSystem alpha beta u z s)
    (hs : UniqueDiffOn ℝ s) (halpha : ContDiffOn ℝ ∞ alpha s)
    (hbeta : ContDiffOn ℝ ∞ beta s) :
    ContDiffOn ℝ ∞ u s ∧ ContDiffOn ℝ ∞ z s := by
  have hdu : DifferentiableOn ℝ u s :=
    fun x hx => (h x hx).1.differentiableAt.differentiableWithinAt
  have hdz : DifferentiableOn ℝ z s :=
    fun x hx => (h x hx).2.differentiableAt.differentiableWithinAt
  have hreg : ∀ n : ℕ, ContDiffOn ℝ n u s ∧ ContDiffOn ℝ n z s := by
    intro n
    induction n with
    | zero =>
      exact ⟨contDiffOn_zero.mpr hdu.continuousOn, contDiffOn_zero.mpr hdz.continuousOn⟩
    | succ n ih =>
      have han : ContDiffOn ℝ n alpha s := (contDiffOn_infty.mp halpha) n
      have hbn : ContDiffOn ℝ n beta s := (contDiffOn_infty.mp hbeta) n
      have hu' : ContDiffOn ℝ n (derivWithin u s) s :=
        (han.mul ih.2).congr
          (fun x hx => (h x hx).1.hasDerivWithinAt.derivWithin (hs x hx))
      have hz' : ContDiffOn ℝ n (derivWithin z s) s :=
        (hbn.mul ih.1).congr
          (fun x hx => (h x hx).2.hasDerivWithinAt.derivWithin (hs x hx))
      have hu_next : ContDiffOn ℝ ((n : ℕ∞ω) + 1) u s :=
        (contDiffOn_succ_iff_derivWithin hs).mpr ⟨hdu, by simp, hu'⟩
      have hz_next : ContDiffOn ℝ ((n : ℕ∞ω) + 1) z s :=
        (contDiffOn_succ_iff_derivWithin hs).mpr ⟨hdz, by simp, hz'⟩
      exact ⟨by simpa only [Nat.cast_add, Nat.cast_one] using hu_next,
        by simpa only [Nat.cast_add, Nat.cast_one] using hz_next⟩
  exact ⟨contDiffOn_infty.mpr (fun n => (hreg n).1),
    contDiffOn_infty.mpr (fun n => (hreg n).2)⟩

theorem outerFirstOrderSystem_physical_flux {s : Set ℝ} {J lam : ℝ}
    {w u z : ℝ → ℝ}
    (h : OuterFirstOrderSystem (fun x => lam / w x)
      (fun x => J * deriv w x / (lam * x)) u z s)
    (hw : ∀ x ∈ s, w x ≠ 0) :
    ∀ x ∈ s, w x * deriv u x = lam * z x := by
  intro x hx
  rw [(h x hx).1.deriv]
  field_simp [hw x hx] <;> ring

/-- The actual first-order physical state solves the original Jacobi equation. -/
theorem outerFirstOrderSystem_radialJacobi {s : Set ℝ} {J lam : ℝ}
    {w u z : ℝ → ℝ} (hs : IsOpen s) (hlam : lam ≠ 0)
    (h : OuterFirstOrderSystem (fun x => lam / w x)
      (fun x => J * deriv w x / (lam * x)) u z s)
    (hw : ∀ x ∈ s, w x ≠ 0) (hr : ∀ x ∈ s, x ≠ 0) :
    ∀ x ∈ s, radialJacobi J w u x = 0 := by
  intro x hx
  have hg : (fun y => w y * deriv u y) =ᶠ[𝓝 x] fun y => lam * z y := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact outerFirstOrderSystem_physical_flux h hw y hy
  have hd : HasDerivAt (fun y => w y * deriv u y)
      (J * deriv w x / x * u x) x := by
    apply (((h x hx).2.const_mul lam).congr_of_eventuallyEq hg).congr_deriv
    field_simp [hlam, hr x hx] <;> ring
  rw [radialJacobi, hd.deriv]
  ring

end ContinuousFlexibility.Radial
