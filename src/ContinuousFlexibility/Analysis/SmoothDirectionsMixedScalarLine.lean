import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine

/-!
# Actual first and mixed scalar derivatives of a directional tower

The zero-jet identity on the open domain turns a tower line derivative
into an ordinary derivative of the actual scalar function.  Differentiating
a first directional derivative along a second direction identifies the
ordered second jet directly, without exchanging partial derivatives.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {U : Set E} {f : E → ℝ}

theorem SmoothDirections.hasDerivAt_line
    (J : SmoothDirections U f) (x w : E) {t : ℝ} (ht : x + t • w ∈ U) :
    HasDerivAt (fun s : ℝ => f (x + s • w))
      (J.D 1 (x + t • w) (fun _ => w)) t := by
  have hc : Continuous (fun s : ℝ => x + s • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
    hc.continuousAt.eventually (J.open_domain.mem_nhds ht)
  have hv : Fin.cons w (Fin.elim0 : Fin 0 → E) = (fun _ : Fin 1 => w) := by
    funext i
    fin_cases i
    rfl
  have hd := J.hasDerivAt_line_jet x w 0 Fin.elim0 ht
  rw [hv] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hmem] with s hs
  exact (J.zero (x + s • w) hs).symm

/-- The order of the two directions is explicit: the outer derivative
occupies the first argument of the genuine second jet. -/
theorem SmoothDirections.hasDerivAt_mixed_scalar_line
    (J : SmoothDirections U f) (x u v : E) (hx : x ∈ U) :
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => f ((x + t • u) + s • v)) 0)
      (J.D 2 x (Fin.cons u (fun _ : Fin 1 => v))) 0 := by
  have hc : Continuous (fun t : ℝ => x + t • u) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • u ∈ U :=
    hc.continuousAt.eventually (J.open_domain.mem_nhds
      (by simpa only [zero_smul, add_zero] using hx))
  have hd : HasDerivAt (fun t : ℝ => J.D 1 (x + t • u) (fun _ : Fin 1 => v))
      (J.D 2 x (Fin.cons u (fun _ : Fin 1 => v))) 0 := by
    simpa only [zero_smul, add_zero] using
      J.hasDerivAt_line_jet x u 1 (fun _ : Fin 1 => v)
        (t := 0) (by simpa only [zero_smul, add_zero] using hx)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hmem] with t ht
  exact J.deriv_line (x + t • u) v ht

theorem SmoothDirections.mixed_scalar_line_deriv
    (J : SmoothDirections U f) (x u v : E) (hx : x ∈ U) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => f ((x + t • u) + s • v)) 0) 0 =
      J.D 2 x (Fin.cons u (fun _ : Fin 1 => v)) :=
  (J.hasDerivAt_mixed_scalar_line x u v hx).deriv

end ContinuousFlexibility.Statements
