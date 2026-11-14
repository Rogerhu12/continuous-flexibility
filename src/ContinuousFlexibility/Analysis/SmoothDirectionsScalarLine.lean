module

public import ContinuousFlexibility.Statements.Analysis

/-!
# Actual scalar derivatives along a line in a smooth directional tower

The scalar iterated derivative is identified with the given continuous
multilinear jet, evaluated repeatedly on the actual direction. This
permits use of the quantitative N01 tower bounds on optical control
curves without substituting a formal derivative.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {U : Set E} {f : E → ℝ}

/-- The tower derivative at a shifted base point is the ordinary scalar
derivative of that same jet along the entire affine line. -/
theorem SmoothDirections.hasDerivAt_line_jet
    (J : SmoothDirections U f) (x w : E) (n : ℕ) (v : Fin n → E)
    {t : ℝ} (ht : x + t • w ∈ U) :
    HasDerivAt (fun s : ℝ => J.D n (x + s • w) v)
      (J.D (n + 1) (x + t • w) (Fin.cons w v)) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have h := J.derivative n (x + t • w) ht v w
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    zero_add, zero_smul, add_zero, add_smul, add_assoc] using h

/-- The neighborhood is open, so the jet identities also hold throughout
a genuine interval around each parameter under consideration. -/
theorem SmoothDirections.iteratedDeriv_line
    (J : SmoothDirections U f) (x w : E) (n : ℕ)
    {t : ℝ} (ht : x + t • w ∈ U) :
    iteratedDeriv n (fun s : ℝ => f (x + s • w)) t =
      J.D n (x + t • w) (fun _ => w) := by
  induction n generalizing t with
  | zero =>
      rw [iteratedDeriv_zero]
      have hv : (fun _ : Fin 0 => w) = Fin.elim0 := Subsingleton.elim _ _
      rw [hv, J.zero _ ht]
  | succ n ih =>
      have hc : Continuous (fun s : ℝ => x + s • w) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hmem : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
        hc.continuousAt.eventually (J.open_domain.mem_nhds ht)
      have heq :
          iteratedDeriv n (fun s : ℝ => f (x + s • w)) =ᶠ[𝓝 t]
            (fun s : ℝ => J.D n (x + s • w) (fun _ => w)) := by
        filter_upwards [hmem] with s hs
        exact ih hs
      rw [iteratedDeriv_succ, heq.deriv_eq,
        (J.hasDerivAt_line_jet x w n (fun _ => w) ht).deriv]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem SmoothDirections.deriv_line
    (J : SmoothDirections U f) (x w : E) (hx : x ∈ U) :
    deriv (fun s : ℝ => f (x + s • w)) 0 = J.D 1 x (fun _ => w) := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, zero_smul, add_zero] using
    J.iteratedDeriv_line x w 1 (t := 0) (by simpa only [zero_smul, add_zero] using hx)

theorem SmoothDirections.deriv_twice_line
    (J : SmoothDirections U f) (x w : E) (hx : x ∈ U) :
    deriv (deriv (fun s : ℝ => f (x + s • w))) 0 =
      J.D 2 x (fun _ => w) := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, zero_smul, add_zero] using
    J.iteratedDeriv_line x w 2 (t := 0) (by simpa only [zero_smul, add_zero] using hx)

end ContinuousFlexibility.Statements
