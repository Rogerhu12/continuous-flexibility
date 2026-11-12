import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
import ContinuousFlexibility.Analysis.N08StateLinearOperations
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Scalar.WeightedStateDerivative
import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The actual scalar nu column

The nu column is an evaluation of the genuine first directional jet of a
represented scalar residual. Its line derivative holds on the full open
domain. At sector states, decoder evaluation and the exact coordinate-line
identity identify it with the frozen `nuColumnField` expression. No
off-sector positivity or extra differentiability premise is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem add_smul_middle_coordinate {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (x : E × (ℝ × F)) (t : ℝ) :
    x + t • (0, ((1 : ℝ), (0 : F))) = (x.1, (x.2.1 + t, x.2.2)) := by
  rcases x with ⟨e, a, f⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, smul_eq_mul, mul_one, add_zero]

private theorem add_smul_fixed_parameter {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : E × ℝ) (v : E) (t : ℝ) : z + t • (v, (0 : ℝ)) = (z.1 + t • v, z.2) := by
  rcases z with ⟨x, q⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]

private theorem eventually_mem_affine_line {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (v : E) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ U := by
  have hc : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  exact ht.eventually (hU.mem_nhds hx)

/-- Abstract coordinate-line calculus keeps the projective carrier out of
all limit simplification and derivative-shift steps. -/
private theorem middle_coordinate_derivative
    {E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    {U : Set ((E × (ℝ × F)) × ℝ)} (hU : IsOpen U)
    (L : G →L[ℝ] ℝ) (f : (E × (ℝ × F)) × ℝ → G)
    (R : (E × (ℝ × F)) × ℝ → ℝ)
    {z : (E × (ℝ × F)) × ℝ} (hz : z ∈ U) {v : G}
    (hd : HasProjectiveLineDerivAt (fun x => f (x, z.2)) v z.1
      ((0 : E), ((1 : ℝ), (0 : F))))
    (hdecode : ∀ a : ℝ, ((z.1.1, (a, z.1.2.2)), z.2) ∈ U →
      L (f ((z.1.1, (a, z.1.2.2)), z.2)) = R ((z.1.1, (a, z.1.2.2)), z.2)) :
    L v = deriv (fun a : ℝ => R ((z.1.1, (a, z.1.2.2)), z.2)) z.1.2.1 := by
  have hraw : HasDerivAt
      (fun t : ℝ => L (f (z.1 + t • ((0 : E), ((1 : ℝ), (0 : F))), z.2))) (L v) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr (hd.clm_comp L)
  have hdpoint : HasDerivAt
      (fun t : ℝ => L (f ((z.1.1, (z.1.2.1 + t, z.1.2.2)), z.2))) (L v) 0 := by
    simpa only [add_smul_middle_coordinate] using hraw
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      ((z.1.1, (z.1.2.1 + t, z.1.2.2)), z.2) ∈ U := by
    simpa only [add_smul_fixed_parameter, add_smul_middle_coordinate] using
      eventually_mem_affine_line hU hz (((0 : E), ((1 : ℝ), (0 : F))), (0 : ℝ))
  have heq : (fun t : ℝ => R ((z.1.1, (z.1.2.1 + t, z.1.2.2)), z.2)) =ᶠ[𝓝 0]
      (fun t : ℝ => L (f ((z.1.1, (z.1.2.1 + t, z.1.2.2)), z.2))) := by
    filter_upwards [hnear] with t ht
    exact (hdecode (z.1.2.1 + t) ht).symm
  have hreal := (hdpoint.congr_of_eventuallyEq heq).deriv
  have hshift := deriv_comp_const_add
    (fun a : ℝ => R ((z.1.1, (a, z.1.2.2)), z.2)) z.1.2.1 (0 : ℝ)
  rw [add_zero] at hshift
  exact hreal.symm.trans hshift

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

def n08NuDirection (S : PhysicalSpacesData) : AnnularState S :=
  (0, ((1 : ℝ), (0, 0)))

theorem n08_add_smul_nuDirection (x : AnnularState S) (t : ℝ) :
    x + (n08StateSMul S t (n08NuDirection S)) = (x.1, (x.2.1 + t, x.2.2)) := by
  simpa only [n08StateSMul, n08RealSMul, n08NuDirection, Prod.zero_eq_mk] using
    add_smul_middle_coordinate x t

theorem n08_stateSector_add_nuDirection {x : AnnularState S}
    (hx : stateSector S x) (t : ℝ) :
    stateSector S (x + (n08StateSMul S t (n08NuDirection S))) := by
  rw [n08_add_smul_nuDirection]
  exact hx

section Realization

variable {U : Set (AnnularState S × ℝ)} {f : AnnularState S × ℝ → S.Source}

/-- An existing actual source derivative is identified by its decoded
nu line. The realization assumption is needed only on the sector. -/
theorem n08_decode_nuDerivative
    (hS : IsPhysicalSpaces D T S) (hU : IsOpen U)
    (hdecode : ∀ z ∈ U, stateSector S z.1 → ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode (f z).val p = scalarResidualField D S C z p)
    {z : AnnularState S × ℝ} (hz : z ∈ U) (hs : stateSector S z.1)
    {v : S.Source}
    (hd : HasProjectiveLineDerivAt (fun x => f (x, z.2)) v z.1 (n08NuDirection S))
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode v.val p = nuColumnField D S C z p := by
  let L : S.Source →L[ℝ] ℝ :=
    ((S.height (3 / 4 : ℝ)).evaluationCLM ((hS.1 (3 / 4 : ℝ)).2.2.1) p).comp
      S.Q.toLinearMap.ker.subtypeL
  have hL (u : S.Source) : L u = (S.height (3 / 4 : ℝ)).decode u.val p := by
    simp only [L, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      SobolevModelData.evaluationCLM_apply]
  rw [← hL v]
  apply middle_coordinate_derivative hU L f (fun y => scalarResidualField D S C y p) hz
  · simpa only [n08NuDirection, Prod.zero_eq_mk] using hd
  · intro a ha
    rw [hL]
    exact hdecode ((z.1.1, (a, z.1.2.2)), z.2) ha hs p hp

/-- The nu column is the genuine first jet in the fixed scalar direction. -/
def n08NuColumn (J : SmoothDirections U f) (z : AnnularState S × ℝ) : S.Source :=
  J.D 1 z (Fin.cons (n08NuDirection S, (0 : ℝ)) Fin.elim0)

/-- This derivative holds for every base point of the open domain,
without a sector restriction. -/
theorem n08NuColumn_hasLineDerivAt (J : SmoothDirections U f)
    {z : AnnularState S × ℝ} (hz : z ∈ U) :
    HasProjectiveLineDerivAt (fun x => f (x, z.2)) (n08NuColumn J z)
      z.1 (n08NuDirection S) := by
  have h := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hz
    (n08NuDirection S, (0 : ℝ))
  rcases z with ⟨x, q⟩
  simpa only [HasProjectiveLineDerivAt, projectiveFirstJetValue, n08NuColumn,
    add_smul_fixed_parameter] using h

theorem n08NuColumn_decode (hS : IsPhysicalSpaces D T S)
    (J : SmoothDirections U f)
    (hdecode : ∀ z ∈ U, stateSector S z.1 → ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode (f z).val p = scalarResidualField D S C z p)
    {z : AnnularState S × ℝ} (hz : z ∈ U) (hs : stateSector S z.1)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode (n08NuColumn J z).val p = nuColumnField D S C z p :=
  n08_decode_nuDerivative hS J.open_domain hdecode hz hs (n08NuColumn_hasLineDerivAt J hz) p hp

end Realization

end ContinuousFlexibility.Statements
