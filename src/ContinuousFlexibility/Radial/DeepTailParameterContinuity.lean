module

public import ContinuousFlexibility.Statements.Radial
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Entrance normalization of the natural tail line

The natural line in the frozen radial interface is specified on the open
tail.  Its entrance value and entrance derivative nevertheless agree for
all smooth representatives of the same line.  The lemmas below make this
one-sided argument explicit before taking parameter limits.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

/-- A constant multiple of a natural solution satisfies the same equation. -/
theorem tailNaturalEquation_const_mul {T : DeepTailData} {u : ℝ → ℝ}
    (hu : TailNaturalEquation T u) (c : ℝ) :
    TailNaturalEquation T (fun x => c * u x) := by
  refine ⟨contDiffAt_const.mul hu.1, contDiffOn_const.mul hu.2.1,
    hu.2.2.1.const_mul c, ?_⟩
  intro x hx
  have hflux : (fun y => T.p y * deriv (fun z => c * u z) y) =
      fun y => c * (T.p y * deriv u y) := by
    funext y
    rw [deriv_const_mul_field]
    ring
  rw [hflux, deriv_const_mul_field]
  calc
    c * deriv (fun y => T.p y * deriv u y) x + T.Λ * T.p x * (c * u x) =
        c * (deriv (fun y => T.p y * deriv u y) x + T.Λ * T.p x * u x) := by ring
    _ = 0 := by rw [hu.2.2.2 x hx, mul_zero]

/-- Continuity transports equality from the open right interval to its
left endpoint; no information to the left of the entrance is needed. -/
theorem tailEntrance_eq_of_eqOn {a b : ℝ} (hab : a < b) {u v : ℝ → ℝ}
    (hu : ContinuousAt u a) (hv : ContinuousAt v a)
    (huv : EqOn u v (Ioo a b)) : u a = v a := by
  have heq : u =ᶠ[𝓝[>] a] v :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hab) fun _ hx => huv hx
  exact tendsto_nhds_unique_of_eventuallyEq
    (hu.mono_left nhdsWithin_le_nhds) (hv.mono_left nhdsWithin_le_nhds) heq

/-- The entrance derivative is also fixed by the open-tail representative. -/
theorem tailEntrance_deriv_eq_of_eqOn {a b : ℝ} (hab : a < b) {u v : ℝ → ℝ}
    (hu : DifferentiableAt ℝ u a) (hv : DifferentiableAt ℝ v a)
    (huv : EqOn u v (Ioo a b)) : deriv u a = deriv v a := by
  have heq : u =ᶠ[𝓝[>] a] v :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hab) fun _ hx => huv hx
  have ha := tailEntrance_eq_of_eqOn hab hu.continuousAt hv.continuousAt huv
  exact (uniqueDiffWithinAt_Ioi a).eq_deriv (Ioi a)
    hu.hasDerivAt.hasDerivWithinAt
    (hv.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq heq ha)

/-- Normalize a representative whose entrance value is nonzero. -/
def tailEntranceNormalize (T : DeepTailData) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (u T.entrance)⁻¹ * u x

theorem tailNaturalEquation_normalize {T : DeepTailData} {u : ℝ → ℝ}
    (hu : TailNaturalEquation T u) :
    TailNaturalEquation T (tailEntranceNormalize T u) :=
  tailNaturalEquation_const_mul hu _

theorem tailEntranceNormalize_entrance {T : DeepTailData} {u : ℝ → ℝ}
    (hu : u T.entrance ≠ 0) : tailEntranceNormalize T u T.entrance = 1 := by
  exact inv_mul_cancel₀ hu

theorem deriv_tailEntranceNormalize (T : DeepTailData) (u : ℝ → ℝ) (x : ℝ) :
    deriv (tailEntranceNormalize T u) x = (u T.entrance)⁻¹ * deriv u x := by
  exact deriv_const_mul_field _

/-- Any nonzero natural solution spans the same line as the witness of
the frozen existential natural-line statement. -/
theorem tailNaturalLine_span_of_nonzero {T : DeepTailData}
    (hline : TailNaturalLineAndKernel T) {u v : ℝ → ℝ}
    (hu : TailNaturalEquation T u) (hv : TailNaturalEquation T v)
    (hune : ∃ x ∈ Ioo T.entrance T.endpoint, u x ≠ 0) :
    ∃ c : ℝ, EqOn v (fun x => c * u x) (Ioo T.entrance T.endpoint) := by
  obtain ⟨w, _, _, hspan, _⟩ := hline
  obtain ⟨cu, hcu⟩ := hspan u hu
  obtain ⟨cv, hcv⟩ := hspan v hv
  obtain ⟨x, hx, hux⟩ := hune
  have hcu₀ : cu ≠ 0 := by
    intro hc
    exact hux (by rw [hcu x hx, hc, zero_mul])
  refine ⟨cv / cu, ?_⟩
  intro y hy
  change v y = (cv / cu) * u y
  rw [hcv y hy, hcu y hy]
  field_simp [hcu₀] <;> ring

theorem tailNaturalLine_span_nonzero {T : DeepTailData}
    (hline : TailNaturalLineAndKernel T) {u v : ℝ → ℝ}
    (hu : TailNaturalEquation T u) (hv : TailNaturalEquation T v)
    (hune : ∃ x ∈ Ioo T.entrance T.endpoint, u x ≠ 0)
    (hvne : ∃ x ∈ Ioo T.entrance T.endpoint, v x ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * u x) (Ioo T.entrance T.endpoint) := by
  obtain ⟨c, hc⟩ := tailNaturalLine_span_of_nonzero hline hu hv hune
  refine ⟨c, ?_, hc⟩
  intro hc₀
  obtain ⟨x, hx, hxne⟩ := hvne
  apply hxne
  simpa only [hc₀, zero_mul] using hc hx

/-- Two natural solutions with entrance value one agree throughout the
closed-at-entrance tail.  The scalar in the abstract natural-line property
is determined by continuity at the entrance. -/
theorem tailNaturalLine_normalized_unique {T : DeepTailData}
    (hab : T.entrance < T.endpoint) (hline : TailNaturalLineAndKernel T)
    {u v : ℝ → ℝ} (hu : TailNaturalEquation T u) (hv : TailNaturalEquation T v)
    (hu₀ : u T.entrance = 1) (hv₀ : v T.entrance = 1) :
    EqOn u v (Ico T.entrance T.endpoint) := by
  obtain ⟨w, hw, _, hspan, _⟩ := hline
  obtain ⟨c, hc⟩ := hspan u hu
  obtain ⟨d, hd⟩ := hspan v hv
  have hc₀ : u T.entrance = c * w T.entrance :=
    tailEntrance_eq_of_eqOn hab hu.1.continuousAt
      (continuousAt_const.mul hw.1.continuousAt) hc
  have hd₀ : v T.entrance = d * w T.entrance :=
    tailEntrance_eq_of_eqOn hab hv.1.continuousAt
      (continuousAt_const.mul hw.1.continuousAt) hd
  have hw₀ : w T.entrance ≠ 0 := by
    intro hwzero
    rw [hu₀, hwzero, mul_zero] at hc₀
    exact one_ne_zero hc₀
  have hcd : c = d := mul_right_cancel₀ hw₀ (by rw [← hc₀, ← hd₀, hu₀, hv₀])
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · rw [← hxa, hu₀, hv₀]
  · rw [hc x ⟨hxa, hx.2⟩, hd x ⟨hxa, hx.2⟩, hcd]

/-- The slope of an entrance-normalized natural solution is independent of
the representative supplied by the existential natural-line theorem. -/
theorem tailNaturalLine_normalized_deriv_unique {T : DeepTailData}
    (hab : T.entrance < T.endpoint) (hline : TailNaturalLineAndKernel T)
    {u v : ℝ → ℝ} (hu : TailNaturalEquation T u) (hv : TailNaturalEquation T v)
    (hu₀ : u T.entrance = 1) (hv₀ : v T.entrance = 1) :
    deriv u T.entrance = deriv v T.entrance := by
  apply tailEntrance_deriv_eq_of_eqOn hab
    (hu.1.differentiableAt (by simp)) (hv.1.differentiableAt (by simp))
  exact (tailNaturalLine_normalized_unique hab hline hu hv hu₀ hv₀).mono Ioo_subset_Ico_self

/-- Continuous value and derivative data give a continuous normalized
slope, provided that normalization does not vanish. -/
theorem continuous_tailEntranceNormalize_slope {P : Type*} [TopologicalSpace P]
    (T : P → DeepTailData) (u : P → ℝ → ℝ)
    (hv : Continuous (fun σ => u σ (T σ).entrance))
    (hd : Continuous (fun σ => deriv (u σ) (T σ).entrance))
    (hn : ∀ σ, u σ (T σ).entrance ≠ 0) :
    Continuous (fun σ => deriv (tailEntranceNormalize (T σ) (u σ)) (T σ).entrance) := by
  simp_rw [deriv_tailEntranceNormalize]
  exact (hv.inv₀ hn).mul hd

end ContinuousFlexibility.Radial
