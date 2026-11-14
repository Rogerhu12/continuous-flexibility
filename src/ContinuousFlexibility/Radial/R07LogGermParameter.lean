module

public import ContinuousFlexibility.Radial.R07JoinParameter
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Logarithmic scale changes on a connected collar

The inverse model coordinate is only specified on its image.  The following
argument needs no formula for its continuation outside that image.  If the
logarithmic height at two different positive scales has smooth germs on a
connected collar, and the underlying height is nonzero at one point, it is
locally nonzero throughout the collar.  Indeed, the difference of the two
logarithms can take only the two values zero and the log scale ratio.

Consequently every positive amplitude has the expected additive logarithmic
shift on every collar germ.  This applies to the already chosen Morse joins.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

/-- Two continuous logarithmic scales detect local nonvanishing throughout
a connected set, even when no regularity of the underlying height is given. -/
theorem eventually_ne_zero_of_two_log_germs {s : Set ℝ} (hs : IsPreconnected s)
    {f F₀ F₁ : ℝ → ℝ} {A₀ A₁ x₀ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hlog : log A₁ - log A₀ ≠ 0)
    (hF₀ : Continuous F₀) (hF₁ : Continuous F₁)
    (hg₀ : ∀ x ∈ s, F₀ =ᶠ[𝓝 x] fun y => log (A₀ * f y))
    (hg₁ : ∀ x ∈ s, F₁ =ᶠ[𝓝 x] fun y => log (A₁ * f y))
    (hx₀ : x₀ ∈ s) (hf₀ : f x₀ ≠ 0) :
    ∀ x ∈ s, ∀ᶠ y in 𝓝 x, f y ≠ 0 := by
  let d : ℝ := log A₁ - log A₀
  let g : ℝ → ℝ := fun x => F₁ x - F₀ x
  have hg : Continuous g := hF₁.sub hF₀
  have hcases (x : ℝ) (hx : x ∈ s) : g x = 0 ∨ g x = d := by
    dsimp only [g]
    rw [(hg₁ x hx).eq_of_nhds, (hg₀ x hx).eq_of_nhds]
    by_cases hf : f x = 0
    · exact Or.inl (by rw [hf, mul_zero, mul_zero, sub_self])
    · apply Or.inr
      rw [log_mul hA₁.ne' hf, log_mul hA₀.ne' hf]
      dsimp only [d]
      ring
  have hmap : MapsTo g s ({0, d} : Set ℝ) := by
    intro x hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcases x hx
  have hbase : g x₀ = d := by
    dsimp only [g]
    rw [(hg₁ x₀ hx₀).eq_of_nhds, (hg₀ x₀ hx₀).eq_of_nhds,
      log_mul hA₁.ne' hf₀, log_mul hA₀.ne' hf₀]
    dsimp only [d]
    ring
  have hconst (x : ℝ) (hx : x ∈ s) : g x = d :=
    (hs.constant_of_mapsTo ((Set.finite_singleton d).insert 0).isDiscrete
      hg.continuousOn hmap hx hx₀).trans hbase
  intro x hx
  have hgn : g x ≠ 0 := by rw [hconst x hx]; exact hlog
  filter_upwards [hg.continuousAt.eventually_ne hgn, hg₀ x hx, hg₁ x hx] with y hy h₀ h₁
  intro hzero
  apply hy
  change F₁ y - F₀ y = 0
  rw [h₁, h₀, hzero, mul_zero, mul_zero, sub_self]

/-- Once nonvanishing is known locally, multiplication by a positive scale
is exactly an additive shift of each chosen smooth logarithmic germ. -/
theorem log_germ_amplitude_shift {s : Set ℝ} {f F F₀ : ℝ → ℝ} {A A₀ : ℝ}
    (hA : 0 < A) (hA₀ : 0 < A₀)
    (hg : ∀ x ∈ s, F =ᶠ[𝓝 x] fun y => log (A * f y))
    (hg₀ : ∀ x ∈ s, F₀ =ᶠ[𝓝 x] fun y => log (A₀ * f y))
    (hfn : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, f y ≠ 0) :
    ∀ x ∈ s, F =ᶠ[𝓝 x] fun y => F₀ y + (log A - log A₀) := by
  intro x hx
  filter_upwards [hg x hx, hg₀ x hx, hfn x hx] with y hy h₀ hn
  rw [hy, h₀, log_mul hA.ne' hn, log_mul hA₀.ne' hn]
  ring

/-- The affine join formula remains valid for arbitrary global extensions
of the logarithmic endpoint germs. -/
theorem morseJoinLog_add_const_of_germs {a b hL hR cL cR : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hab : a ≤ b) (hhL : 0 < hL) (hhR : 0 < hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fun y => fL y + cL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fun y => fR y + cR)
    {x : ℝ} (hx : x ∈ Icc a b) :
    morseJoinLog a b hL hR FL FR x =
      morseJoinLog a b hL hR fL fR x + cL +
        (cR - cL) * morseJoinHeightCoordinate a b hL hR x := by
  rw [morseJoinLog_eqOn_of_germs hab hhL hhR hLg hRg hx,
    morseJoinLog_add_const hfL hfR]

end ContinuousFlexibility.Radial
