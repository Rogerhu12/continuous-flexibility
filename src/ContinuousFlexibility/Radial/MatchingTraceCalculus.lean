import ContinuousFlexibility.Radial.MatchingGraphRepresentatives
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# One-sided matching trace calculus

The outer graph is regular on its two half-closed physical components.
Near a matching cut those components and the closure of the outer region
have the same germ. This gives the actual within-derivative trace
calculus without regularity at the physical endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff BigOperators
open ContinuousFlexibility.Statements

theorem matchingCut_mem_innerIcc {D : ReferenceData}
    {M : RadialMatchingData D} (hm : M.innerLeft < M.innerRight) (i : Fin 2) :
    matchingCut D M i ∈ Icc M.innerLeft M.innerRight := by
  unfold matchingCut
  split_ifs
  · exact ⟨le_rfl, hm.le⟩
  · exact ⟨hm.le, le_rfl⟩

theorem matchingCut_mem_core_of_geometry {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b) (i : Fin 2) :
    matchingCut D M i ∈ radialCore D := by
  have hi := matchingCut_mem_innerIcc hm i
  exact ⟨ha.trans_le hi.1, hi.2.trans_lt hb⟩

theorem matchingCut_mem_outerOneSided {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hb : M.innerRight < D.b) (i : Fin 2) :
    matchingCut D M i ∈ Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b := by
  unfold matchingCut
  split_ifs
  · exact Or.inl ⟨ha, le_rfl⟩
  · exact Or.inr ⟨le_rfl, hb⟩

theorem matchingOuter_uniqueDiffWithinAt {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hb : M.innerRight < D.b) (i : Fin 2) :
    UniqueDiffWithinAt ℝ (closure (matchingOuterRegion D M)) (matchingCut D M i) := by
  rw [matchingOuterRegion_closure ha hb]
  unfold matchingCut
  split_ifs
  · exact ((uniqueDiffOn_Icc ha).uniqueDiffWithinAt ⟨ha.le, le_rfl⟩).mono subset_union_left
  · exact ((uniqueDiffOn_Icc hb).uniqueDiffWithinAt ⟨le_rfl, hb.le⟩).mono subset_union_right

theorem matchingOuter_oneSided_mem_nhdsWithin {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b) (i : Fin 2) :
    (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∈
      𝓝[closure (matchingOuterRegion D M)] (matchingCut D M i) := by
  have hcore : radialCore D ∈ 𝓝 (matchingCut D M i) :=
    isOpen_Ioo.mem_nhds (matchingCut_mem_core_of_geometry ha hm hb i)
  filter_upwards [nhdsWithin_le_nhds hcore, self_mem_nhdsWithin] with x hx hxT
  rw [matchingOuterRegion_closure ha hb] at hxT
  rcases hxT with hxT | hxT
  · exact Or.inl ⟨hx.1, hxT.2⟩
  · exact Or.inr ⟨hxT.1, hx.2⟩

theorem matchingOuter_differentiableWithinAt {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (i : Fin 2) :
    DifferentiableWithinAt ℝ u (closure (matchingOuterRegion D M)) (matchingCut D M i) := by
  have hd := (hu (matchingCut D M i) (matchingCut_mem_outerOneSided ha hb i)).differentiableWithinAt
    one_ne_zero
  exact hd.mono_of_mem_nhdsWithin (matchingOuter_oneSided_mem_nhdsWithin ha hm hb i)

theorem matchingInnerFlux_congr {D : ReferenceData}
    {M : RadialMatchingData D} (hm : M.innerLeft < M.innerRight)
    {u v : ℝ → ℝ} (huv : EqOn u v (Icc M.innerLeft M.innerRight))
    (i : Fin 2) :
    matchingInnerFlux D M u i = matchingInnerFlux D M v i := by
  unfold matchingInnerFlux
  rw [derivWithin_congr huv (huv (matchingCut_mem_innerIcc hm i))]

theorem matchingOuterFlux_congr {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {u v : ℝ → ℝ} (huv : EqOn u v (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (i : Fin 2) :
    matchingOuterFlux D M u i = matchingOuterFlux D M v i := by
  have heq : u =ᶠ[𝓝[closure (matchingOuterRegion D M)] (matchingCut D M i)] v := by
    filter_upwards [matchingOuter_oneSided_mem_nhdsWithin ha hm hb i] with x hx
    exact huv hx
  unfold matchingOuterFlux
  rw [heq.derivWithin_eq (huv (matchingCut_mem_outerOneSided ha hb i))]

theorem matchingInnerFlux_const_mul (D : ReferenceData) (M : RadialMatchingData D)
    (c : ℝ) (u : ℝ → ℝ) (i : Fin 2) :
    matchingInnerFlux D M (fun x => c * u x) i =
      c * matchingInnerFlux D M u i := by
  unfold matchingInnerFlux
  rw [derivWithin_const_mul_field]
  ring

theorem matchingOuterFlux_const_mul (D : ReferenceData) (M : RadialMatchingData D)
    (c : ℝ) (u : ℝ → ℝ) (i : Fin 2) :
    matchingOuterFlux D M (fun x => c * u x) i =
      c * matchingOuterFlux D M u i := by
  unfold matchingOuterFlux
  rw [derivWithin_const_mul_field]
  ring

theorem matchingInnerFlux_sub {D : ReferenceData}
    {M : RadialMatchingData D} (hm : M.innerLeft < M.innerRight)
    {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight))
    (hv : ContDiffOn ℝ 1 v (Icc M.innerLeft M.innerRight))
    (i : Fin 2) :
    matchingInnerFlux D M (fun x => u x - v x) i =
      matchingInnerFlux D M u i - matchingInnerFlux D M v i := by
  have hmem := matchingCut_mem_innerIcc hm i
  have hdu := (hu (matchingCut D M i) hmem).differentiableWithinAt one_ne_zero
  have hdv := (hv (matchingCut D M i) hmem).differentiableWithinAt one_ne_zero
  unfold matchingInnerFlux
  rw [derivWithin_fun_sub hdu hdv]
  ring

theorem matchingOuterFlux_sub {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (hv : ContDiffOn ℝ 1 v (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (i : Fin 2) :
    matchingOuterFlux D M (fun x => u x - v x) i =
      matchingOuterFlux D M u i - matchingOuterFlux D M v i := by
  unfold matchingOuterFlux
  rw [derivWithin_fun_sub
    (matchingOuter_differentiableWithinAt ha hm hb hu i)
    (matchingOuter_differentiableWithinAt ha hm hb hv i)]
  ring

theorem matchingInnerFlux_fun_sum {D : ReferenceData}
    {M : RadialMatchingData D} (hm : M.innerLeft < M.innerRight)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (u : ι → ℝ → ℝ)
    (hu : ∀ k, ContDiffOn ℝ 1 (u k) (Icc M.innerLeft M.innerRight))
    (i : Fin 2) :
    matchingInnerFlux D M (fun x => ∑ k, c k * u k x) i =
      ∑ k, c k * matchingInnerFlux D M (u k) i := by
  classical
  have hd (k : ι) : DifferentiableWithinAt ℝ (fun x => c k * u k x)
      (Icc M.innerLeft M.innerRight) (matchingCut D M i) := by
    have hk := (hu k (matchingCut D M i) (matchingCut_mem_innerIcc hm i)).differentiableWithinAt
      one_ne_zero
    exact hk.const_mul (c k)
  unfold matchingInnerFlux
  rw [derivWithin_fun_sum (fun k _ => hd k)]
  simp only [derivWithin_const_mul_field, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem matchingOuterFlux_fun_sum {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (u : ι → ℝ → ℝ)
    (hu : ∀ k, ContDiffOn ℝ 1 (u k)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (i : Fin 2) :
    matchingOuterFlux D M (fun x => ∑ k, c k * u k x) i =
      ∑ k, c k * matchingOuterFlux D M (u k) i := by
  classical
  have hd (k : ι) : DifferentiableWithinAt ℝ (fun x => c k * u k x)
      (closure (matchingOuterRegion D M)) (matchingCut D M i) :=
    (matchingOuter_differentiableWithinAt ha hm hb (hu k) i).const_mul (c k)
  unfold matchingOuterFlux
  rw [derivWithin_fun_sum (fun k _ => hd k)]
  simp only [derivWithin_const_mul_field, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- A representative that is C1 throughout the core has matching inner
and outer flux traces at either regular cut. -/
theorem matchingInnerFlux_eq_outerFlux {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (radialCore D)) (i : Fin 2) :
    matchingInnerFlux D M u i = matchingOuterFlux D M u i := by
  have hcore := matchingCut_mem_core_of_geometry ha hm hb i
  have hd : DifferentiableAt ℝ u (matchingCut D M i) :=
    (hu.contDiffAt (isOpen_Ioo.mem_nhds hcore)).differentiableAt one_ne_zero
  have hinner : UniqueDiffWithinAt ℝ (Icc M.innerLeft M.innerRight) (matchingCut D M i) :=
    (uniqueDiffOn_Icc hm).uniqueDiffWithinAt (matchingCut_mem_innerIcc hm i)
  unfold matchingInnerFlux matchingOuterFlux
  rw [hd.derivWithin hinner, hd.derivWithin (matchingOuter_uniqueDiffWithinAt ha hb i)]

/-- Trimming the distant physical endpoint leaves the left cut derivative
unchanged, with no regularity hypothesis on the function. -/
theorem matchingOuter_derivWithin_left {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {l0 : ℝ} (h0 : D.a < l0) (hL : l0 < M.innerLeft) (u : ℝ → ℝ) :
    derivWithin u (Icc l0 M.innerLeft) M.innerLeft =
      derivWithin u (closure (matchingOuterRegion D M)) M.innerLeft := by
  apply derivWithin_congr_set
  rw [matchingOuterRegion_closure ha hb]
  filter_upwards [Ioo_mem_nhds hL hm] with x hx
  apply propext
  constructor
  · intro h
    exact Or.inl ⟨h0.le.trans h.1, h.2⟩
  · rintro (h | h)
    · exact ⟨hx.1.le, h.2⟩
    · exact False.elim ((not_le_of_gt hx.2) h.1)

/-- Trimming the distant physical endpoint leaves the right cut derivative
unchanged, with no regularity hypothesis on the function. -/
theorem matchingOuter_derivWithin_right {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {r0 : ℝ} (hR : M.innerRight < r0) (h1 : r0 < D.b) (u : ℝ → ℝ) :
    derivWithin u (Icc M.innerRight r0) M.innerRight =
      derivWithin u (closure (matchingOuterRegion D M)) M.innerRight := by
  apply derivWithin_congr_set
  rw [matchingOuterRegion_closure ha hb]
  filter_upwards [Ioo_mem_nhds hm hR] with x hx
  apply propext
  constructor
  · intro h
    exact Or.inr ⟨h.1, h.2.trans h1.le⟩
  · rintro (h | h)
    · exact False.elim ((not_le_of_gt hx.1) h.2)
    · exact ⟨h.1, hx.2.le⟩

end ContinuousFlexibility.Radial
