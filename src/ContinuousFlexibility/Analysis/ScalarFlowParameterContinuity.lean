module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Tactic.Ring

/-!
# Continuous dependence of scalar trajectories on external parameters

A parameter is a constant component of an augmented trajectory.  The
ordinary two-trajectory Gronwall estimate then controls parameter-dependent
solutions without any assumed parameter derivative or pre-existing
continuous choice of solutions.

The derivative hypotheses are within the full closed time interval, exactly
as supplied by the Picard-Lindelof existence theorem.  The initial time is the
left endpoint.  A Lipschitz initial-value map gives a uniform parameter
Lipschitz bound and joint continuity on the parameter-time domain.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace ContinuousFlexibility.Analysis

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The actual parameter-dependent trajectories satisfy the augmented
Gronwall estimate.  No continuity in the external parameter is assumed. -/
theorem dist_scalarFlow_parameters_le
    {S : Set P} {F : P → ℝ → ℝ → ℝ} {u : P → ℝ → ℝ} {v : P → ℝ}
    {a b : ℝ} {K : ℝ≥0}
    (hF : ∀ t ∈ Ico a b,
      LipschitzOnWith K (fun x : P × ℝ => F x.1 t x.2) (S ×ˢ univ))
    (hdu : ∀ p ∈ S, ∀ t ∈ Icc a b,
      HasDerivWithinAt (u p) (F p t (u p t)) (Icc a b) t)
    (hinit : ∀ p ∈ S, u p a = v p)
    {p q : P} (hp : p ∈ S) (hq : q ∈ S)
    {t : ℝ} (ht : t ∈ Icc a b) :
    dist (u p t) (u q t) ≤
      max (dist p q) (dist (v p) (v q)) * Real.exp ((K : ℝ) * (t - a)) := by
  have hfield : ∀ r ∈ Ico a b,
      LipschitzOnWith K
        (fun x : P × ℝ => ((0 : P), F x.1 r x.2)) (S ×ˢ univ) := by
    intro r hr
    simpa only [max_eq_right (show (0 : ℝ≥0) ≤ K from zero_le)] using
      (LipschitzWith.const (0 : P)).lipschitzOnWith.prodMk (hF r hr)
  have hc (x : P) (hx : x ∈ S) :
      ContinuousOn (fun r => (x, u x r)) (Icc a b) :=
    continuousOn_const.prodMk (HasDerivWithinAt.continuousOn (hdu x hx))
  have hd (x : P) (hx : x ∈ S) (r : ℝ) (hr : r ∈ Ico a b) :
      HasDerivWithinAt (fun s => (x, u x s))
        ((0 : P), F x r (u x r)) (Ici r) r := by
    have hn : Icc a b ∈ 𝓝[Ici r] r :=
      Filter.mem_of_superset (Icc_mem_nhdsGE hr.2) (Icc_subset_Icc_left hr.1)
    exact (hasDerivAt_const r x).hasDerivWithinAt.prodMk
      ((hdu x hx r ⟨hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin hn)
  have hdist :=
    dist_le_of_trajectories_ODE_of_mem hfield (hc p hp) (hd p hp)
      (fun _ _ => ⟨hp, mem_univ _⟩) (hc q hq) (hd q hq)
      (fun _ _ => ⟨hq, mem_univ _⟩)
      (show dist (p, u p a) (q, u q a) ≤
        max (dist p q) (dist (v p) (v q)) by
          rw [Prod.dist_eq, hinit p hp, hinit q hq]) t ht
  exact (le_max_right (dist p q) (dist (u p t) (u q t))).trans
    (by simpa only [Prod.dist_eq] using hdist)

/-- A uniform parameter Lipschitz constant on the entire time interval.
The factor is explicit and depends only on the two Lipschitz constants
and the length of the interval. -/
theorem lipschitzOnWith_scalarFlow_parameters
    {S : Set P} {F : P → ℝ → ℝ → ℝ} {u : P → ℝ → ℝ} {v : P → ℝ}
    {a b : ℝ} {K L : ℝ≥0}
    (hF : ∀ t ∈ Ico a b,
      LipschitzOnWith K (fun x : P × ℝ => F x.1 t x.2) (S ×ˢ univ))
    (hdu : ∀ p ∈ S, ∀ t ∈ Icc a b,
      HasDerivWithinAt (u p) (F p t (u p t)) (Icc a b) t)
    (hinit : ∀ p ∈ S, u p a = v p)
    (hv : LipschitzOnWith L v S)
    {t : ℝ} (ht : t ∈ Icc a b) :
    LipschitzOnWith
      (NNReal.mk (max 1 (L : ℝ) * Real.exp ((K : ℝ) * (b - a)))
        (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le))
      (fun p => u p t) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  have hinitial :
      max (dist p q) (dist (v p) (v q)) ≤ max 1 (L : ℝ) * dist p q := by
    apply max_le
    · calc
        dist p q = 1 * dist p q := (one_mul _).symm
        _ ≤ max 1 (L : ℝ) * dist p q :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    · exact (hv.dist_le_mul p hp q hq).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)
  have hexp : Real.exp ((K : ℝ) * (t - a)) ≤ Real.exp ((K : ℝ) * (b - a)) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) K.2)
  have hbound := dist_scalarFlow_parameters_le hF hdu hinit hp hq ht
  simp only [NNReal.coe_mk]
  calc
    dist (u p t) (u q t) ≤
        max (dist p q) (dist (v p) (v q)) * Real.exp ((K : ℝ) * (t - a)) := hbound
    _ ≤ (max 1 (L : ℝ) * dist p q) * Real.exp ((K : ℝ) * (b - a)) :=
      mul_le_mul hinitial hexp (Real.exp_pos _).le
        (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) dist_nonneg)
    _ = (max 1 (L : ℝ) * Real.exp ((K : ℝ) * (b - a))) * dist p q := by ring

/-- Any actual family satisfying these hypotheses is jointly continuous;
continuity of the choice made when constructing the trajectories is
derived from the ODE estimate. -/
theorem continuousOn_scalarFlow_parameters_time
    {S : Set P} {F : P → ℝ → ℝ → ℝ} {u : P → ℝ → ℝ} {v : P → ℝ}
    {a b : ℝ} {K L : ℝ≥0}
    (hF : ∀ t ∈ Ico a b,
      LipschitzOnWith K (fun x : P × ℝ => F x.1 t x.2) (S ×ˢ univ))
    (hdu : ∀ p ∈ S, ∀ t ∈ Icc a b,
      HasDerivWithinAt (u p) (F p t (u p t)) (Icc a b) t)
    (hinit : ∀ p ∈ S, u p a = v p)
    (hv : LipschitzOnWith L v S) :
    ContinuousOn (fun x : P × ℝ => u x.1 x.2) (S ×ˢ Icc a b) := by
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _
    (NNReal.mk (max 1 (L : ℝ) * Real.exp ((K : ℝ) * (b - a)))
      (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le))
  · intro p hp
    exact HasDerivWithinAt.continuousOn (hdu p hp)
  · intro t ht
    exact lipschitzOnWith_scalarFlow_parameters hF hdu hinit hv ht

end ContinuousFlexibility.Analysis
