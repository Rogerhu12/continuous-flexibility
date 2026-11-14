module

public import ContinuousFlexibility.Analysis.ScalarDerivativeLimit
public import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine

/-!
# Pointwise limits of every jet in a directional tower

Pointwise convergence of the actual zero jets and local uniform bounds
on the next two jets force convergence of every directional jet. The
argument differentiates scalar affine lines and uses the uniform Taylor
remainder, rather than assuming endpoint derivatives already exist.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {ι : Type*} {l : Filter ι} [NeBot l]
  {U : Set E} {f : ι → E → ℝ}

/-- A local bound on the second line derivative transfers the next
directional jet, including its actual scalar derivative identity. -/
theorem exists_tendsto_next_directional_jet
    (J : ∀ i, SmoothDirections U (f i)) {n : ℕ} {g : E → ℝ}
    (x : E) (v : Fin n → E) (w : E)
    (hg : ∀ y ∈ U, Tendsto (fun i => (J i).D n y v) l (𝓝 (g y)))
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hmem : ∀ t : ℝ, |t| < δ → x + t • w ∈ U)
    (hbound : ∀ i t, |t| < δ →
      |(J i).D (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v))| ≤ B) :
    ∃ a : ℝ,
      Tendsto (fun i => (J i).D (n + 1) x (Fin.cons w v)) l (𝓝 a) ∧
      HasDerivAt (fun t : ℝ => g (x + t • w)) a 0 := by
  apply exists_tendsto_derivative_of_uniform_slope_error
    (f := fun i t => (J i).D n (x + t • w) v)
    (d := fun i => (J i).D (n + 1) x (Fin.cons w v))
    (δ := δ) (B := B) hδ hB
  · intro t ht
    simpa only [zero_add] using hg (x + t • w) (hmem t ht)
  · intro i h hh hne
    have he := abs_slope_sub_derivative_le_of_second_derivative_bound
      (f := fun t => (J i).D n (x + t • w) v)
      (f' := fun t => (J i).D (n + 1) (x + t • w) (Fin.cons w v))
      (f'' := fun t => (J i).D (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v)))
      hδ hB
      (fun t ht => (J i).hasDerivAt_line_jet x w n v (hmem t ht))
      (fun t ht => (J i).hasDerivAt_line_jet x w (n + 1) (Fin.cons w v) (hmem t ht))
      (hbound i) hh hne
    simpa only [zero_add, zero_smul, add_zero] using he

/-- All pointwise directional jets converge. A separate equicontinuity
argument is needed when assembling continuous multilinear endpoint jets. -/
theorem exists_tendsto_all_directional_jets
    (J : ∀ i, SmoothDirections U (f i)) {g : E → ℝ}
    (hzero : ∀ x ∈ U, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hbound : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧
        (∀ t : ℝ, |t| < δ → x + t • w ∈ U) ∧
        ∀ i t, |t| < δ →
          |(J i).D (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v))| ≤ B) :
    ∀ n x, x ∈ U → ∀ v : Fin n → E,
      ∃ a : ℝ, Tendsto (fun i => (J i).D n x v) l (𝓝 a) := by
  classical
  intro n
  induction n with
  | zero =>
      intro x hx v
      refine ⟨g x, ?_⟩
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      simpa only [hv, (J _).zero x hx] using hzero x hx
  | succ n ih =>
      intro x hx v
      let G : E → ℝ := fun y => if hy : y ∈ U then
        (ih y hy (Fin.tail v)).choose else 0
      have hG (y : E) (hy : y ∈ U) :
          Tendsto (fun i => (J i).D n y (Fin.tail v)) l (𝓝 (G y)) := by
        dsimp only [G]
        rw [dif_pos hy]
        exact (ih y hy (Fin.tail v)).choose_spec
      obtain ⟨δ, B, hδ, hB, hmem, hsecond⟩ := hbound n x hx (Fin.tail v) (v 0)
      obtain ⟨a, ha, _⟩ := exists_tendsto_next_directional_jet J x (Fin.tail v) (v 0)
        hG hδ hB hmem hsecond
      exact ⟨a, by simpa only [Fin.cons_self_tail] using ha⟩

end ContinuousFlexibility.Analysis
