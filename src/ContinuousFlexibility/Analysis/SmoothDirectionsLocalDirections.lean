import ContinuousFlexibility.Analysis.SmoothDirectionsMixedScalarLine
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Propagating equality of genuine directional derivatives

If two first directions give the same actual first jet throughout an
open domain, differentiating that identity along arbitrary parameter
lines preserves it at every order. The final direction is kept explicit.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

local instance smoothDirectionsLocalDirectionsRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {U : Set E} {f : E → ℝ}

theorem SmoothDirections.continuousAt_jet_eval
    (J : SmoothDirections U f) (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    ContinuousAt (fun y => J.D n y v) x := by
  have hc : ContinuousAt (fun p : E × (Fin n → E) => J.D n p.1 p.2) (x, v) :=
    (J.continuous n).continuousAt
      ((J.open_domain.prod isOpen_univ).mem_nhds
        (show (x, v) ∈ U ×ˢ univ from ⟨hx, mem_univ v⟩))
  have hmap : ContinuousAt (fun y : E => (y, v)) x :=
    continuousAt_id.prodMk continuousAt_const
  simpa only [Function.comp_def] using hc.comp_of_eq hmap rfl

theorem SmoothDirections.abs_jet_sub_le_of_next_bound
    (J : SmoothDirections U f) (n : ℕ) (x w : E) (v : Fin n → E)
    (q A : ℝ)
    (hline : ∀ t ∈ uIcc (0 : ℝ) q, x + t • w ∈ U)
    (hbound : ∀ t ∈ uIcc (0 : ℝ) q,
      |J.D (n + 1) (x + t • w) (Fin.cons w v)| ≤ A) :
    |J.D n (x + q • w) v - J.D n x v| ≤ A * |q| := by
  have hb := (convex_uIcc (0 : ℝ) q).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (J.hasDerivAt_line_jet x w n v (hline t ht)).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t ht)
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 q) (right_mem_uIcc : q ∈ uIcc 0 q)
  simpa only [zero_smul, add_zero, Real.norm_eq_abs, sub_zero] using hb

theorem SmoothDirections.snoc_jet_eq_of_first_jet_eq
    (J : SmoothDirections U f) (u v : E)
    (hfirst : ∀ x ∈ U, J.D 1 x (fun _ => u) = J.D 1 x (fun _ => v))
    (n : ℕ) (x : E) (hx : x ∈ U) (w : Fin n → E) :
    J.D (n + 1) x (Fin.snoc w u) = J.D (n + 1) x (Fin.snoc w v) := by
  induction n generalizing x with
  | zero => simpa only [Fin.snoc_zero] using hfirst x hx
  | succ n ih =>
      have hc : Continuous (fun t : ℝ => x + t • w 0) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • w 0 ∈ U :=
        hc.continuousAt.eventually (J.open_domain.mem_nhds
          (by simpa only [zero_smul, add_zero] using hx))
      have heq :
          (fun t : ℝ => J.D (n + 1) (x + t • w 0) (Fin.snoc (Fin.tail w) u)) =ᶠ[𝓝 0]
          (fun t : ℝ => J.D (n + 1) (x + t • w 0) (Fin.snoc (Fin.tail w) v)) := by
        filter_upwards [hmem] with t ht
        exact ih (x + t • w 0) ht (Fin.tail w)
      have hzero : x + (0 : ℝ) • w 0 ∈ U := by
        simpa only [zero_smul, add_zero] using hx
      have hdu := J.hasDerivAt_line_jet x (w 0) (n + 1)
        (Fin.snoc (Fin.tail w) u) hzero
      have hdv := J.hasDerivAt_line_jet x (w 0) (n + 1)
        (Fin.snoc (Fin.tail w) v) hzero
      have hd := heq.deriv_eq
      rw [hdu.deriv, hdv.deriv] at hd
      simpa only [zero_smul, add_zero, Fin.cons_snoc_eq_snoc_cons,
        Fin.cons_self_tail] using hd

end ContinuousFlexibility.Statements
