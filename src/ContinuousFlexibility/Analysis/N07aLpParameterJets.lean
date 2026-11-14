module

public import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative
public import ContinuousFlexibility.Statements.Analysis

/-!
# Measurability and continuity of actual parameter jets in L²

Measurability of higher parameter derivatives follows from their genuine
difference quotients. No interchange of parameter and spatial derivatives
is needed. Locally dominated pointwise continuity then gives continuity in
the actual L² norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ENNReal
open ContinuousFlexibility.Statements

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : E → α → ℝ}

/-- All genuine parameter jets are measurable in the auxiliary spatial
variable once the original field is measurable. -/
theorem n07a_smoothDirections_aestronglyMeasurable
    (hU : IsOpen U) (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (hf : ∀ x ∈ U, AEStronglyMeasurable (f x) μ) :
    ∀ (k : ℕ) (x : E), x ∈ U → ∀ v : Fin k → E,
      AEStronglyMeasurable (fun a => (J a).D k x v) μ := by
  classical
  intro k
  induction k with
  | zero =>
      intro x hx v
      have hv : v = Fin.elim0 := by funext i; exact i.elim0
      simpa only [hv, fun a => (J a).zero x hx] using hf x hx
  | succ k ih =>
      intro x hx v
      let w : E := v 0
      let u : Fin k → E := fun i => v i.succ
      have hv : v = Fin.cons w u := by
        funext i
        refine Fin.cases ?_ ?_ i <;> simp [w, u]
      rw [hv]
      let F (t : ℝ) (a : α) : ℝ :=
        if x + t • w ∈ U then (J a).D k (x + t • w) u else 0
      have hF (t : ℝ) : AEStronglyMeasurable (F t) μ := by
        by_cases ht : x + t • w ∈ U
        · simpa only [F, ite_eq_left ht] using ih (x + t • w) ht u
        · simp only [F, ite_eq_right ht]
          exact aestronglyMeasurable_const
      have hc : Continuous (fun t : ℝ => x + t • w) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have ht : Tendsto (fun t : ℝ => x + t • w) (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
        simpa only [zero_smul, add_zero] using
          (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℝ), x + t • w ∈ U :=
        ht.eventually (hU.mem_nhds hx)
      apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ))
        (fun t => ((hF t).sub (ih x hx u)).const_smul t⁻¹)
      filter_upwards [] with a
      have hd := (J a).derivative k x hx u w
      simp only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
        zero_add, zero_smul, add_zero] at hd
      apply hd.congr'
      filter_upwards [hnear] with t ht
      simp only [F, ite_eq_left ht, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

/-- A locally square-integrable pointwise majorant upgrades pointwise
continuity to continuity of the actual L² classes. -/
theorem n07a_continuousOn_toLp [FirstCountableTopology E]
    (hf : ∀ x : E, MemLp (f x) 2 μ)
    (hpoint : ∀ a : α, ContinuousOn (fun x => f x a) U)
    (hbound : ∀ x ∈ U, ∃ g : α → ℝ, MemLp g 2 μ ∧
      ∀ᶠ y in 𝓝[U] x, ∀ᵐ a ∂μ, |f y a| ≤ g a) :
    ContinuousOn (fun x => (hf x).toLp (f x)) U := by
  intro x hx
  obtain ⟨g, hg, hb⟩ := hbound x hx
  apply spaces_tendsto_toLp_of_dominated hf (hf x) (hg.add (hf x).norm)
  · filter_upwards [hb] with y hy
    filter_upwards [hy] with a ha
    calc
      |f y a - f x a| ≤ |f y a| + |f x a| := abs_sub _ _
      _ ≤ g a + ‖f x a‖ := by simpa only [Real.norm_eq_abs] using add_le_add ha (le_refl |f x a|)
  · exact Filter.Eventually.of_forall fun a => hpoint a x hx

end ContinuousFlexibility.Analysis
