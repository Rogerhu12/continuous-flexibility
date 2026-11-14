import ContinuousFlexibility.Analysis.N07aLpParameterJets
import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Genuine parameter jets through a dominated scalar integral

The scalar output already has its algebraic directional tower. Equality
with an integral at order zero identifies every higher jet. Measurability
comes from genuine difference quotients; a continuous numerical majorant
supplies domination along each scalar line inside the original open set.
No spatial continuity of the higher parameter jets is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : E → α → ℝ} {g : E → ℝ}

/-- A scalar integral identity and locally bounded genuine input jets
determine all jets of the actual scalar output on the same open set. -/
theorem n04Realization_smoothDirections_integral_jets
    (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (Q : SmoothDirections U g)
    (hvalue : ∀ x ∈ U, g x = ∫ a, f x a ∂μ)
    (hf : ∀ x ∈ U, AEStronglyMeasurable (f x) μ)
    (G : ∀ k : ℕ, E × (Fin k → E) → ℝ)
    (hG : ∀ k, Continuous (G k))
    (hbound : ∀ k x, x ∈ U → ∀ (v : Fin k → E) a,
      |(J a).D k x v| ≤ G k (x, v)) :
    ∀ k x, x ∈ U → ∀ v : Fin k → E,
      Q.D k x v = ∫ a, (J a).D k x v ∂μ := by
  have hmeas := n07a_smoothDirections_aestronglyMeasurable Q.open_domain J hf
  have hmem (k : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E) :
      Integrable (fun a => (J a).D k x v) μ := by
    apply (integrable_const |G k (x, v)|).mono' (hmeas k x hx v)
    exact Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs] using (hbound k x hx v a).trans (le_abs_self _)
  intro k
  induction k with
  | zero =>
      intro x hx v
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv, Q.zero x hx, hvalue x hx]
      apply integral_congr_ae
      exact Eventually.of_forall fun a => ((J a).zero x hx).symm
  | succ k ih =>
      intro x hx v
      let w : E := v 0
      let u : Fin k → E := fun i => v i.succ
      have hv : v = Fin.cons w u := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero, w]
        · simp only [Fin.cons_succ, u]
      rw [hv]
      let B : ℝ := |G (k + 1) (x, Fin.cons w u)| + 1
      have hline : Continuous (fun t : ℝ => x + t • w) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hline0 : Tendsto (fun t : ℝ => x + t • w) (𝓝 0) (𝓝 x) := by
        simpa only [zero_smul, add_zero] using hline.tendsto 0
      have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • w ∈ U :=
        hline0.eventually (Q.open_domain.mem_nhds hx)
      have hGlineContinuous : Continuous
          (fun t : ℝ => G (k + 1) (x + t • w, Fin.cons w u)) :=
        (hG (k + 1)).comp (hline.prodMk continuous_const)
      have hGline : Tendsto
          (fun t : ℝ => G (k + 1) (x + t • w, Fin.cons w u))
          (𝓝 0) (𝓝 (G (k + 1) (x, Fin.cons w u))) := by
        simpa only [zero_smul, add_zero] using hGlineContinuous.tendsto 0
      have hnearBound : ∀ᶠ t in 𝓝 (0 : ℝ),
          G (k + 1) (x + t • w, Fin.cons w u) ≤ B :=
        hGline.eventually_le_const ((le_abs_self _).trans_lt (lt_add_one _))
      let V : Set ℝ := {t | x + t • w ∈ U ∧
        G (k + 1) (x + t • w, Fin.cons w u) ≤ B}
      have hV : V ∈ 𝓝 (0 : ℝ) := hnear.and hnearBound
      have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := μ) (x₀ := (0 : ℝ)) (s := V)
        (F := fun t a => (J a).D k (x + t • w) u)
        (F' := fun t a => (J a).D (k + 1) (x + t • w) (Fin.cons w u))
        (bound := fun _ : α => B) hV
        (hnear.mono (fun t ht => hmeas k (x + t • w) ht u))
        (by simpa only [zero_smul, add_zero] using hmem k x hx u)
        (by simpa only [zero_smul, add_zero] using hmeas (k + 1) x hx (Fin.cons w u))
        (Eventually.of_forall fun a t ht => by
          simpa only [Real.norm_eq_abs] using
            (hbound (k + 1) (x + t • w) ht.1 (Fin.cons w u) a).trans ht.2)
        (integrable_const B)
        (Eventually.of_forall fun a t ht =>
          (J a).hasDerivAt_line_jet x w k u ht.1)).2
      have heq : (fun t : ℝ => Q.D k (x + t • w) u) =ᶠ[𝓝 0]
          (fun t : ℝ => ∫ a, (J a).D k (x + t • w) u ∂μ) :=
        hnear.mono (fun t ht => ih (x + t • w) ht u)
      have hQ := Q.hasDerivAt_line_jet x w k u
        (t := 0) (by simpa only [zero_smul, add_zero] using hx)
      simpa only [zero_smul, add_zero] using hQ.unique (hd.congr_of_eventuallyEq heq)

end ContinuousFlexibility.Analysis
