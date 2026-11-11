import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

def n08NuDirection (S : PhysicalSpacesData) : AnnularState S :=
  (0, ((1 : ℝ), (0, 0)))

theorem n08_add_smul_nuDirection (x : AnnularState S) (t : ℝ) :
    x + (@SMul.smul ℝ (AnnularState S) _ t (n08NuDirection S)) = (x.1, (x.2.1 + t, x.2.2)) :=
  add_smul_middle_coordinate x t

theorem n08_stateSector_add_nuDirection {x : AnnularState S}
    (hx : stateSector S x) (t : ℝ) :
    stateSector S (x + (@SMul.smul ℝ (AnnularState S) _ t (n08NuDirection S))) := by
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
  have hdpoint : HasDerivAt
      (fun t : ℝ => (S.height (3 / 4 : ℝ)).decode
        (f (z.1 + (@SMul.smul ℝ (AnnularState S) _ t (n08NuDirection S)), z.2)).val p)
      ((S.height (3 / 4 : ℝ)).decode v.val p) 0 := by
    simpa only [Submodule.subtypeL_apply] using
      sobolev_decode_hasDerivAt_of_projectiveLineDerivAt
        (A := S.height (3 / 4 : ℝ))
        ((hS.1 (3 / 4 : ℝ)).2.2.1) (hd.clm_comp S.Q.toLinearMap.ker.subtypeL) p
  have hnear := eventually_mem_affine_line hU hz (n08NuDirection S, (0 : ℝ))
  have heq : (fun t : ℝ => scalarResidualField D S C
      (z.1 + (@SMul.smul ℝ (AnnularState S) _ t (n08NuDirection S)), z.2) p) =ᶠ[𝓝 0]
      (fun t : ℝ => (S.height (3 / 4 : ℝ)).decode
        (f (z.1 + (@SMul.smul ℝ (AnnularState S) _ t (n08NuDirection S)), z.2)).val p) := by
    filter_upwards [hnear] with t ht
    have ht' : (z.1 + (@SMul.smul ℝ (AnnularState S) _ t (n08NuDirection S)), z.2) ∈ U := by
      simpa only [add_smul_fixed_parameter] using ht
    exact (hdecode _ ht' (n08_stateSector_add_nuDirection hs t) p hp).symm
  have hreal := (hdpoint.congr_of_eventuallyEq heq).deriv
  simp only [n08_add_smul_nuDirection] at hreal
  have hshift := deriv_comp_const_add
    (fun a : ℝ => scalarResidualField D S C ((z.1.1, (a, z.1.2.2)), z.2) p)
    z.1.2.1 (0 : ℝ)
  rw [add_zero] at hshift
  exact hreal.symm.trans hshift

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
