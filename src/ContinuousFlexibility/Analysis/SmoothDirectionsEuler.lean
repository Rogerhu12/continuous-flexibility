import ContinuousFlexibility.Analysis.SmoothDirectionsLocalDirections

/-!
# Euler identities in an actual directional tower

An actual first-order scaling identity propagates through every scalar
derivative. Multiplying the kth scalar jet by the kth power of the line
parameter then gives a nonsingular bound by one mixed height jet. The
argument includes a zero scalar parameter and never divides by it.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {U : Set E} {f : E → ℝ}

private theorem euler_cons_const (w : E) (n : ℕ) :
    Fin.cons w (fun _ : Fin n => w) = (fun _ : Fin (n + 1) => w) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem SmoothDirections.euler_scalar_jet
    (J : SmoothDirections U f) (x w u : E)
    (heuler : ∀ q : ℝ, x + q • w ∈ U →
      J.D 1 (x + q • w) (fun _ => u) = q * J.D 1 (x + q • w) (fun _ => w))
    (n : ℕ) (q : ℝ) (hq : x + q • w ∈ U) :
    J.D (n + 1) (x + q • w) (Fin.snoc (fun _ : Fin n => w) u) =
      q * J.D (n + 1) (x + q • w) (fun _ => w) +
        (n : ℝ) * J.D n (x + q • w) (fun _ => w) := by
  induction n generalizing q with
  | zero =>
      simpa only [Fin.snoc_zero, Nat.cast_zero, zero_mul, add_zero] using heuler q hq
  | succ n ih =>
      have hc : Continuous (fun s : ℝ => x + s • w) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hmem : ∀ᶠ s in 𝓝 q, x + s • w ∈ U :=
        hc.continuousAt.eventually (J.open_domain.mem_nhds hq)
      have heq :
          (fun s : ℝ => J.D (n + 1) (x + s • w)
            (Fin.snoc (fun _ : Fin n => w) u)) =ᶠ[𝓝 q]
          (fun s : ℝ => s * J.D (n + 1) (x + s • w) (fun _ => w) +
            (n : ℝ) * J.D n (x + s • w) (fun _ => w)) := by
        filter_upwards [hmem] with s hs
        exact ih s hs
      have hleft := J.hasDerivAt_line_jet x w (n + 1)
        (Fin.snoc (fun _ : Fin n => w) u) hq
      have hnext := J.hasDerivAt_line_jet x w (n + 1) (fun _ => w) hq
      have hprev := J.hasDerivAt_line_jet x w n (fun _ => w) hq
      have hright := ((hasDerivAt_id q).fun_mul hnext).fun_add (hprev.const_mul (n : ℝ))
      have hd := heq.deriv_eq
      rw [hleft.deriv, hright.deriv] at hd
      simp only [Fin.cons_snoc_eq_snoc_cons, euler_cons_const, one_mul] at hd
      calc
        _ = _ := hd
        _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

/-- A uniform bound for the next mixed jet bounds the pure scalar jet
with no scalar denominator and no exclusion of the origin. -/
theorem SmoothDirections.abs_pure_scalar_jet_le_of_mixed_euler_bound
    (J : SmoothDirections U f) (x w u : E)
    (heuler : ∀ q : ℝ, x + q • w ∈ U →
      J.D 1 (x + q • w) (fun _ => u) = q * J.D 1 (x + q • w) (fun _ => w))
    (n : ℕ) (q A : ℝ)
    (hline : ∀ t ∈ Icc (0 : ℝ) 1, x + (t * q) • w ∈ U)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |J.D (n + 2) (x + (t * q) • w)
        (Fin.snoc (fun _ : Fin (n + 1) => w) u)| ≤ A) :
    |J.D (n + 1) (x + q • w) (fun _ => w)| ≤ A := by
  let g : ℝ → ℝ := fun t => t ^ (n + 1) *
    J.D (n + 1) (x + (t * q) • w) (fun _ => w)
  let g' : ℝ → ℝ := fun t => t ^ n * J.D (n + 2) (x + (t * q) • w)
    (Fin.snoc (fun _ : Fin (n + 1) => w) u)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g' t) t := by
    have hj := J.hasDerivAt_line_jet x w (n + 1) (fun _ => w) (hline t ht)
    have hj' : HasDerivAt
        (fun a : ℝ => J.D (n + 1) (x + (a * q) • w) (fun _ => w))
        (J.D (n + 2) (x + (t * q) • w) (fun _ => w) * q) t := by
      simpa only [Function.comp_def, euler_cons_const, one_mul] using
        hj.comp t ((hasDerivAt_id t).mul_const q)
    have hp := ((hasDerivAt_id t).pow (n + 1)).fun_mul hj'
    apply hp.congr_deriv
    have he := J.euler_scalar_jet x w u heuler (n + 1) (t * q) (hline t ht)
    dsimp only [g']
    rw [he, pow_succ]
    ring
  have hg' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖g' t‖ ≤ A := by
    have hp : 0 ≤ t ^ n := pow_nonneg ht.1 n
    have hp1 : t ^ n ≤ 1 := pow_le_one₀ ht.1 ht.2
    change ‖t ^ n * J.D (n + 2) (x + (t * q) • w)
      (Fin.snoc (fun _ : Fin (n + 1) => w) u)‖ ≤ A
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    exact (mul_le_mul hp1 (hbound t ht) (abs_nonneg _) zero_le_one).trans_eq (one_mul A)
  have hb := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hg'
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa only [g, one_pow, one_mul, zero_pow (Nat.succ_ne_zero n), zero_mul,
    sub_zero, Real.norm_eq_abs, abs_one, mul_one] using hb

end ContinuousFlexibility.Statements
