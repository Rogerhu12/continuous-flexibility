module

public import ContinuousFlexibility.Analysis.ProjectiveNewtonRecurrence
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Convergence and residual closure of the actual Newton iterates

Summable increments in every projective grade give a limit of the same
sequence in the compatible Banach coordinates. A fixed closed margin
keeps the limit inside the open Newton cylinder. Forward smoothing and
strong approximation make every sufficiently high base grade separating.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section ProjectiveConvergence

variable {E : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, CompleteSpace (E n)]
  {bond : ∀ n, E (n + 1) →L[ℝ] E n}

/-- Absolute summability of the increments in every actual grade implies
convergence in the compatible product topology. -/
theorem tendsto_projectiveLimit_of_summable_graded_increments
    {u : ℕ → ProjectiveLimit E bond}
    (hu : ∀ s, Summable (fun n => gradedSeminorm E bond s (u (n + 1) - u n))) :
    ∃ x : ProjectiveLimit E bond, Tendsto u atTop (𝓝 x) := by
  classical
  have hcoord (s : ℕ) : ∃ x : E s,
      Tendsto (fun n => (u n).1 s) atTop (𝓝 x) := by
    let v (n : ℕ) := (u n).1 s
    have hv : Summable (fun n => dist (v n) (v (n + 1))) := by
      apply Summable.of_nonneg_of_le (fun _ => dist_nonneg) _ (hu s)
      intro n
      rw [dist_comm (v n), dist_eq_norm]
      change ‖(u (n + 1) - u n).1 s‖ ≤ gradedSeminorm E bond s (u (n + 1) - u n)
      exact norm_coordinate_le_graded E bond le_rfl _
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hv)
  choose x hx using hcoord
  have hcompat (s : ℕ) : bond s (x (s + 1)) = x s := by
    have h : Tendsto (fun n => bond s ((u n).1 (s + 1))) atTop (𝓝 (bond s (x (s + 1)))) :=
      ((bond s).continuous.tendsto (x (s + 1))).comp (hx (s + 1))
    have h' : Tendsto (fun n => (u n).1 s) atTop (𝓝 (bond s (x (s + 1)))) :=
      h.congr' (Eventually.of_forall fun n => (u n).2 s)
    exact tendsto_nhds_unique h' (hx s)
  let y : ProjectiveLimit E bond := ⟨x, hcompat⟩
  exact ⟨y, (tendsto_projectiveLimit_iff E bond (f := u) (x := y)).mpr hx⟩

/-- Summable actual corrections give a limit of the original smoothed
Newton sequence at its unchanged real parameter. -/
theorem projectiveSmoothedNewtonIterates_tendsto_of_summable_corrections
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (R : ProjectiveLimit E bond × ℝ → Y)
    (V : ProjectiveLimit E bond × ℝ → Y →ₗ[ℝ] ProjectiveLimit E bond)
    (S : ℕ → ProjectiveLimit E bond →L[ℝ] ProjectiveLimit E bond)
    (N : ℕ → ℕ) (z₀ : ProjectiveLimit E bond × ℝ) :
    let z := projectiveSmoothedNewtonIterates R V S N z₀
    (∀ s, Summable (fun n => gradedSeminorm E bond s (S (N n) (V (z n) (R (z n)))))) →
      ∃ x : ProjectiveLimit E bond, Tendsto z atTop (𝓝 (x, z₀.2)) := by
  dsimp only
  let z := projectiveSmoothedNewtonIterates R V S N z₀
  intro hs
  have hinc (s : ℕ) :
      Summable (fun n => gradedSeminorm E bond s ((z (n + 1)).1 - (z n).1)) := by
    have he : (fun n => gradedSeminorm E bond s ((z (n + 1)).1 - (z n).1)) =
        fun n => gradedSeminorm E bond s (S (N n) (V (z n) (R (z n)))) := by
      funext n
      let d := S (N n) (V (z n) (R (z n)))
      change gradedSeminorm E bond s (((z n).1 - d) - (z n).1) = gradedSeminorm E bond s d
      rw [show (z n).1 - d - (z n).1 = -d by abel, map_neg_eq_map]
    rw [he]
    exact hs s
  obtain ⟨x, hx⟩ :=
    tendsto_projectiveLimit_of_summable_graded_increments (u := fun n => (z n).1) hinc
  have hpair : Tendsto (fun n => ((z n).1, z₀.2)) atTop (𝓝 (x, z₀.2)) :=
    hx.prodMk_nhds tendsto_const_nhds
  refine ⟨x, hpair.congr' (Eventually.of_forall fun n => ?_)⟩
  exact Prod.ext rfl (projectiveSmoothedNewtonIterates_parameter R V S N z₀ n).symm

end ProjectiveConvergence

section Separation

variable {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [T1Space Y]
  {q : ℕ → Seminorm ℝ Y}

/-- For a fixed smoothing family, a base grade controlling every smoothed
higher grade already separates points. -/
theorem eq_zero_of_grade_eq_zero_of_forward_smoothing
    (hq : WithSeminorms q) (hmono : Monotone q)
    (B : ℕ) (S : ℕ → Y →L[ℝ] Y)
    (happrox : ∀ y, Tendsto (fun N => S N y) atTop (𝓝 y))
    (hforward : ∀ s, B ≤ s → ∃ K : ℕ → ℝ, ∀ N y, q s (S N y) ≤ K N * q B y)
    {y : Y} (hy : q B y = 0) : y = 0 := by
  by_contra hne
  obtain ⟨s, hs⟩ := hq.separating_of_T1 y hne
  let m := max B s
  obtain ⟨K, hK⟩ := hforward m (le_max_left B s)
  have hzero (N : ℕ) : q m (S N y) = 0 := by
    refine le_antisymm ?_ (apply_nonneg (q m) _)
    simpa only [hy, mul_zero] using hK N y
  have hlim : Tendsto (fun N => q m (S N y)) atTop (𝓝 (q m y)) :=
    ((hq.continuous_seminorm m).tendsto y).comp (happrox y)
  have hlim₀ : Tendsto (fun N => q m (S N y)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hm : q m y = 0 := tendsto_nhds_unique hlim hlim₀
  exact hs (le_antisymm ((hmono (le_max_right B s) y).trans_eq hm) (apply_nonneg (q s) _))

/-- The actual smoothing estimates and approximation provide a separating
base grade and all larger separating grades. -/
theorem exists_separating_grade_of_hasSmoothing
    (hq : WithSeminorms q) (hmono : Monotone q) (hS : Statements.HasSmoothing q) :
    ∃ b : ℕ, ∀ B : ℕ, b ≤ B → ∀ y : Y, q B y = 0 → y = 0 := by
  obtain ⟨b, loss, S, hforward, _, happrox⟩ := hS
  refine ⟨b, fun B hB y hy => ?_⟩
  apply eq_zero_of_grade_eq_zero_of_forward_smoothing hq hmono B S happrox _ hy
  intro s hs
  obtain ⟨C, _, hC⟩ := hforward B s hB hs
  exact ⟨fun N => C * Real.exp (((s : ℝ) - B + loss) * N), hC⟩

end Separation

section LimitClosure

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X]

/-- A closed seminorm radius persists under convergence in the actual
space topology. -/
theorem seminorm_sub_le_of_tendsto
    (p : Seminorm ℝ X) (hp : Continuous p) (x₀ : X) {δ : ℝ}
    {u : ℕ → X} {x : X} (hu : Tendsto u atTop (𝓝 x))
    (hclosed : ∀ n, p (u n - x₀) ≤ δ) : p (x - x₀) ≤ δ := by
  have hc : Continuous (fun y : X => p (y - x₀)) :=
    hp.comp (continuous_id.sub continuous_const)
  exact le_of_tendsto' ((hc.tendsto x).comp hu) hclosed

/-- A strict gap between the closed margin and the open cylinder keeps
the limit inside the domain of the residual. -/
theorem mem_newton_cylinder_of_tendsto
    (p : Seminorm ℝ X) (hp : Continuous p) (x₀ : X) {δ ε : ℝ}
    {z : ℕ → X × ℝ} {zLim : X × ℝ} (hz : Tendsto z atTop (𝓝 zLim))
    (hδε : δ < ε) (hclosed : ∀ n, p ((z n).1 - x₀) ≤ δ ∧ |(z n).2| ≤ δ) :
    zLim ∈ {w : X × ℝ | p (w.1 - x₀) < ε ∧ |w.2| < ε} := by
  have hstate : p (zLim.1 - x₀) ≤ δ :=
    seminorm_sub_le_of_tendsto p hp x₀
      ((continuous_fst.tendsto zLim).comp hz) (fun n => (hclosed n).1)
  have hparam : |zLim.2| ≤ δ := by
    have hc : Continuous (fun w : X × ℝ => |w.2|) := continuous_abs.comp continuous_snd
    exact le_of_tendsto' ((hc.tendsto zLim).comp hz) (fun n => (hclosed n).2)
  exact ⟨hstate.trans_lt hδε, hparam.trans_lt hδε⟩

end LimitClosure

/-- The residual vanishes at the limit if it is continuous within the
domain and decays in one separating seminorm along the sequence. -/
theorem residual_eq_zero_of_tendsto_of_separating_seminorm
    {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    [AddCommGroup Y] [Module ℝ Y]
    {R : Z → Y} {U : Set Z} {z : ℕ → Z} {zLim : Z}
    (hR : ContinuousOn R U) (hz : Tendsto z atTop (𝓝 zLim)) (hzLim : zLim ∈ U)
    (hzin : ∀ᶠ n in atTop, z n ∈ U) (q : Seminorm ℝ Y) (hq : Continuous q)
    (hsep : ∀ y, q y = 0 → y = 0)
    (hdecay : Tendsto (fun n => q (R (z n))) atTop (𝓝 0)) : R zLim = 0 := by
  have hwithin : Tendsto z atTop (𝓝[U] zLim) := tendsto_nhdsWithin_iff.mpr ⟨hz, hzin⟩
  have hRlim : Tendsto (fun n => R (z n)) atTop (𝓝 (R zLim)) :=
    (hR zLim hzLim).tendsto.comp hwithin
  have hqRlim : Tendsto (fun n => q (R (z n))) atTop (𝓝 (q (R zLim))) :=
    (hq.tendsto (R zLim)).comp hRlim
  exact hsep (R zLim) (tendsto_nhds_unique hqRlim hdecay)

/-- Conditional closure of the actual Newton iteration. The summability,
closed margin and low residual decay all refer to the same iterates. -/
theorem exists_projectiveSmoothedNewton_limit_zero
    {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, CompleteSpace (E n)] {bond : ∀ n, E (n + 1) →L[ℝ] E n}
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    (R : ProjectiveLimit E bond × ℝ → Y)
    (V : ProjectiveLimit E bond × ℝ → Y →ₗ[ℝ] ProjectiveLimit E bond)
    (S : ℕ → ProjectiveLimit E bond →L[ℝ] ProjectiveLimit E bond)
    (N : ℕ → ℕ) (z₀ : ProjectiveLimit E bond × ℝ)
    (p : Seminorm ℝ (ProjectiveLimit E bond)) (hp : Continuous p)
    (x₀ : ProjectiveLimit E bond) {δ ε : ℝ} (hδε : δ < ε)
    (q : Seminorm ℝ Y) (hq : Continuous q) (hsep : ∀ y, q y = 0 → y = 0) :
    let z := projectiveSmoothedNewtonIterates R V S N z₀
    let U : Set (ProjectiveLimit E bond × ℝ) :=
      {w | p (w.1 - x₀) < ε ∧ |w.2| < ε}
    ContinuousOn R U →
    (∀ s, Summable (fun n => gradedSeminorm E bond s (S (N n) (V (z n) (R (z n)))))) →
    (∀ n, p ((z n).1 - x₀) ≤ δ ∧ |(z n).2| ≤ δ) →
    Tendsto (fun n => q (R (z n))) atTop (𝓝 0) →
    ∃ x : ProjectiveLimit E bond,
      Tendsto z atTop (𝓝 (x, z₀.2)) ∧ (x, z₀.2) ∈ U ∧ R (x, z₀.2) = 0 := by
  dsimp only
  intro hR hsum hclosed hdecay
  obtain ⟨x, hx⟩ :=
    projectiveSmoothedNewtonIterates_tendsto_of_summable_corrections R V S N z₀ hsum
  have hin := mem_newton_cylinder_of_tendsto p hp x₀ hx hδε hclosed
  refine ⟨x, hx, hin, residual_eq_zero_of_tendsto_of_separating_seminorm hR hx hin ?_
    q hq hsep hdecay⟩
  exact Eventually.of_forall fun n => ⟨(hclosed n).1.trans_lt hδε, (hclosed n).2.trans_lt hδε⟩

end ContinuousFlexibility.Analysis
