import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Smooth tame maps with values in a closed subspace

If the values of a smooth map on its open domain lie in a closed linear
subspace, so do all its actual directional derivatives there.  Restricting
the codomain therefore preserves the full smooth tame tower and its grading
estimates.  The globally defined subspace-valued representative only needs
to agree with the original map on that open domain.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

section ClosedRange

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]

/-- An actual directional derivative stays in a closed linear subspace
containing the values near its base point. -/
theorem solve_lineDeriv_mem_submodule
    (W : Submodule ℝ Y) (hW : IsClosed (W : Set Y))
    {U : Set X} (hU : IsOpen U) {f : X → Y}
    (hf : ∀ x ∈ U, f x ∈ W) {x v : X} {df : Y}
    (hx : x ∈ U) (hd : HasProjectiveLineDerivAt f df x v) : df ∈ W := by
  have hc : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), x + t • v ∈ U := ht.eventually (hU.mem_nhds hx)
  simp only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    zero_add, zero_smul, add_zero] at hd
  exact hW.mem_of_tendsto hd (hev.mono fun t ht =>
    W.smul_mem (t⁻¹) (W.sub_mem (hf _ ht) (hf x hx)))

/-- Every member of a genuine directional derivative tower takes values
in the same closed linear subspace on the open domain. -/
theorem solve_smoothDirections_mem_submodule
    (W : Submodule ℝ Y) (hW : IsClosed (W : Set Y))
    {U : Set X} {f : X → Y} (J : SmoothDirections U f)
    (hf : ∀ x ∈ U, f x ∈ W) :
    ∀ k x, x ∈ U → ∀ v : Fin k → X, J.D k x v ∈ W := by
  intro k
  induction k with
  | zero =>
      intro x hx v
      have hv : v = Fin.elim0 := by funext i; exact i.elim0
      rw [hv, J.zero x hx]
      exact hf x hx
  | succ k ih =>
      intro x hx v
      have hv : v = Fin.cons (v 0) (fun i : Fin k => v i.succ) := by
        funext i
        refine Fin.cases ?_ ?_ i <;> simp
      rw [hv]
      exact solve_lineDeriv_mem_submodule W hW J.open_domain
        (fun y hy => ih y hy (fun i => v i.succ)) hx
        (J.derivative k x hx (fun i => v i.succ) (v 0))

/-- Codomain restriction does not require agreement away from the open
domain. In particular it applies to a representative set to zero outside
the neighborhood on which an inverse is tangent to an affine slice. -/
theorem solve_smoothTameOn_codRestrict
    (W : Submodule ℝ Y) (hW : IsClosed (W : Set Y))
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {U : Set X} {f : X → Y} (h : SmoothTameOn p q U f)
    (g : X → W) (hg : ∀ x ∈ U, (g x : Y) = f x) :
    SmoothTameOn p (fun n => (q n).comp W.subtype) U g := by
  classical
  obtain ⟨J, hJ⟩ := h
  have hf : ∀ x ∈ U, f x ∈ W := by
    intro x hx
    rw [← hg x hx]
    exact (g x).property
  have hjet := solve_smoothDirections_mem_submodule W hW J hf
  let K : ∀ n : ℕ, X → X [×n]→L[ℝ] W := fun n x =>
    if hx : x ∈ U then (J.D n x).codRestrict W (hjet n x hx) else 0
  have hK (n : ℕ) (x : X) (hx : x ∈ U) (v : Fin n → X) :
      (K n x v : Y) = J.D n x v := by
    dsimp only [K]
    rw [dif_pos hx]
    exact ContinuousMultilinearMap.codRestrict_apply_coe _ _ _ _
  let Jg : SmoothDirections U g :=
    { open_domain := J.open_domain
      D := K
      zero := by
        intro x hx
        apply Subtype.ext
        rw [hK 0 x hx, J.zero x hx, hg x hx]
      continuous := by
        intro n
        apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        exact (J.continuous n).congr fun z hz => hK n z.1 hz.1 z.2
      derivative := by
        intro n x hx v w
        have hc : Continuous (fun t : ℝ => x + t • w) :=
          continuous_const.add (continuous_id.smul continuous_const)
        have ht : Tendsto (fun t : ℝ => x + t • w) (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
          simpa only [zero_smul, add_zero] using
            (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), x + t • w ∈ U :=
          ht.eventually (J.open_domain.mem_nhds hx)
        have hd := J.derivative n x hx v w
        simp only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
          zero_add, zero_smul, add_zero] at hd ⊢
        apply tendsto_subtype_rng.mpr
        simp only [Submodule.coe_smul, Submodule.coe_sub, hK (n + 1) x hx]
        apply hd.congr'
        filter_upwards [hev] with t ht
        rw [hK n (x + t • w) ht, hK n x hx] }
  refine ⟨Jg, fun k x0 hx0 => ?_⟩
  obtain ⟨loss, base, ε, hε, hs⟩ := hJ k x0 hx0
  refine ⟨loss, base, ε, hε, fun s hs' => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hs s hs'
  refine ⟨C, hC, fun x hx hxε v => ?_⟩
  change (q s).comp W.subtype (K k x v) ≤ _
  rw [Seminorm.comp_apply, Submodule.subtype_apply, hK k x hx]
  exact hbound x hx hxε v

end ClosedRange

end ContinuousFlexibility.Analysis
