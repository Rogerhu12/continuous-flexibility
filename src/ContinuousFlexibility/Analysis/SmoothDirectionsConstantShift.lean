module

public import ContinuousFlexibility.Analysis.SmoothDirectionsMixedScalarLine

/-!
# Positive genuine jets are unchanged by a constant shift

The assertion follows by differentiating the actual scalar identities
on the open parameter domain. No choice of a special constant tower or
formal derivative convention is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f g : E → ℝ}

theorem SmoothDirections.positive_jet_eq_of_constant_shift
    (J : SmoothDirections U f) (K : SmoothDirections U g) (c : ℝ)
    (heq : ∀ x ∈ U, f x = g x + c)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin (n + 1) → E) :
    J.D (n + 1) x v = K.D (n + 1) x v := by
  induction n generalizing x with
  | zero =>
      have hzero : x + (0 : ℝ) • v 0 ∈ U := by
        simpa only [zero_smul, add_zero] using hx
      have hmem : ∀ᶠ t : ℝ in 𝓝 0, x + t • v 0 ∈ U :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
          (J.open_domain.mem_nhds hzero)
      have hline : (fun t : ℝ => f (x + t • v 0)) =ᶠ[𝓝 0]
          (fun t : ℝ => g (x + t • v 0) + c) := by
        filter_upwards [hmem] with t ht
        exact heq _ ht
      have hJ := J.hasDerivAt_line x (v 0) hzero
      have hK := (K.hasDerivAt_line x (v 0) hzero).add_const c
      have hd := hline.deriv_eq
      rw [hJ.deriv, hK.deriv] at hd
      have hv : (fun _ : Fin 1 => v 0) = v :=
        funext (fun i => congrArg v (Subsingleton.elim (0 : Fin 1) i))
      simpa only [zero_smul, add_zero, hv] using hd
  | succ n ih =>
      have hzero : x + (0 : ℝ) • v 0 ∈ U := by
        simpa only [zero_smul, add_zero] using hx
      have hmem : ∀ᶠ t : ℝ in 𝓝 0, x + t • v 0 ∈ U :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
          (J.open_domain.mem_nhds hzero)
      have hline :
          (fun t : ℝ => J.D (n + 1) (x + t • v 0) (Fin.tail v)) =ᶠ[𝓝 0]
          (fun t : ℝ => K.D (n + 1) (x + t • v 0) (Fin.tail v)) := by
        filter_upwards [hmem] with t ht
        exact ih _ ht (Fin.tail v)
      have hJ := J.hasDerivAt_line_jet x (v 0) (n + 1) (Fin.tail v) hzero
      have hK := K.hasDerivAt_line_jet x (v 0) (n + 1) (Fin.tail v) hzero
      have hd := hline.deriv_eq
      rw [hJ.deriv, hK.deriv] at hd
      simpa only [zero_smul, add_zero, Fin.cons_self_tail] using hd

end ContinuousFlexibility.Statements
