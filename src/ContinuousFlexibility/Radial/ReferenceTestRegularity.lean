module

public import ContinuousFlexibility.Radial.RadialHeight
public import ContinuousFlexibility.Radial.ReferenceLocalL2

/-!
# Regularity and support of the actual weak-test operator

The radial PDE is the actual derivative expression from FourierModes.
Its apparent singular coefficient at r = 0 causes no problem for an
admissible test: the test and all of its radial slices vanish on a
neighborhood of that radius. The same compact radial support controls
the test after applying the operator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

theorem radialPDE_zero_of_radial_support
    {K : Set ℝ} (hK : IsClosed K) {ψ : PolarPoint → ℝ}
    (hs : ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0)
    (w : ℝ → ℝ) {r : ℝ} (hr : r ∉ K) (θ : ℝ) :
    Radial.radialPDE w (fun t φ => ψ (t, φ)) r θ = 0 := by
  have hd (t : ℝ) (ht : t ∉ K) : deriv (fun z => ψ (z, θ)) t = 0 := by
    have he : (fun z => ψ (z, θ)) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hK.isOpen_compl.mem_nhds ht] with z hz
      exact hs z hz θ
    simpa only [deriv_const] using he.deriv_eq
  have hflux : (fun t => w t * deriv (fun z => ψ (z, θ)) t) =ᶠ[𝓝 r]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hr] with t ht
    rw [hd t ht, mul_zero]
  have hfd : deriv (fun t => w t * deriv (fun z => ψ (z, θ)) t) r = 0 := by
    simpa only [deriv_const] using hflux.deriv_eq
  have hθ : (fun φ => ψ (r, φ)) = (fun _ => (0 : ℝ)) :=
    funext (fun φ => hs r hr φ)
  have hz : deriv (fun _ : ℝ => (0 : ℝ)) = (fun _ : ℝ => (0 : ℝ)) := by
    funext φ
    exact deriv_const φ (0 : ℝ)
  change deriv (fun t => w t * deriv (fun z => ψ (z, θ)) t) r +
    deriv w r / r * deriv (deriv (fun φ => ψ (r, φ))) θ = 0
  rw [hfd, hθ, hz]
  simp only [deriv_const, mul_zero, add_zero]

theorem radialPDE_continuousAt_of_ne_zero
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    {ψ : PolarPoint → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {x : PolarPoint} (hx : x.1 ≠ 0) :
    ContinuousAt (fun y : PolarPoint =>
      Radial.radialPDE w (fun r θ => ψ (r, θ)) y.1 y.2) x := by
  have hdw : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw).2
  have hwr := (hw.continuous.comp continuous_fst).continuousAt (x := x)
  have hdwr := (hdw.continuous.comp continuous_fst).continuousAt (x := x)
  have hr : ContDiffAt ℝ ∞ (radialPartial ψ) x :=
    contDiffAt_radialPartial hψ.contDiffAt (by simp)
  have hrr : ContDiffAt ℝ ∞ (radialPartial (radialPartial ψ)) x :=
    contDiffAt_radialPartial hr (by simp)
  have ht : ContDiffAt ℝ ∞ (angularPartial ψ) x :=
    contDiffAt_angularPartial hψ.contDiffAt (by simp)
  have htt : ContDiffAt ℝ ∞ (angularPartial (angularPartial ψ)) x :=
    contDiffAt_angularPartial ht (by simp)
  have h := ((hdwr.mul hr.continuousAt).add (hwr.mul hrr.continuousAt)).add
    ((hdwr.div continuous_fst.continuousAt hx).mul htt.continuousAt)
  apply h.congr
  exact Eventually.of_forall (fun y =>
    (Radial.radialPDE_eq_polar_jets (hw.differentiable (by simp) y.1) hψ).symm)

/-- The actual PDE applied to an admissible test is continuous on the
whole coordinate plane and has the same compact radial support. -/
theorem RadialTest.operator_continuous {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) :
    Continuous (fun x : PolarPoint =>
      Radial.radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2) := by
  obtain ⟨C, hC⟩ := hD
  obtain ⟨hψ, _, K, hK, hKcore, hs⟩ := hψ
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.1 ∈ K
  · exact radialPDE_continuousAt_of_ne_zero hC.1.2.2.1.1 hψ
      (ne_of_gt (hC.1.1.trans (hKcore hx).1))
  · have he : (fun y : PolarPoint =>
        Radial.radialPDE D.w (fun r θ => ψ (r, θ)) y.1 y.2) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [((hK.isClosed.isOpen_compl).preimage continuous_fst).mem_nhds hx]
        with y hy
      exact radialPDE_zero_of_radial_support hK.isClosed hs D.w hy y.2
    exact continuousAt_const.congr he.symm

theorem RadialTest.operator_radial_support {D : ReferenceData}
    {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, ∀ θ,
        Radial.radialPDE D.w (fun t φ => ψ (t, φ)) r θ = 0 := by
  obtain ⟨_, _, K, hK, hKcore, hs⟩ := hψ
  exact ⟨K, hK, hKcore, fun r hr θ =>
    radialPDE_zero_of_radial_support hK.isClosed hs D.w hr θ⟩

end ContinuousFlexibility.Statements
