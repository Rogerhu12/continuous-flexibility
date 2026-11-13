import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPhysicalPower
import ContinuousFlexibility.Analysis.N04RealizationFactoredRootTraceDirections

/-!
# Genuine radial trace identities under inward orientation

The affine radial coordinate acts on each genuine radial jet by its
scalar power. This identity is an identity of the whole angular trace,
so it also transports every mixed parameter and angular derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

theorem n04PositiveGeometry_radialBoundaryJet_rootShift
    {f : PolarPoint → ℝ} {r σ θ : ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f (r, θ)) :
    radialBoundaryJet (fun p => f (rootProfileShift r σ p)) 0 n θ =
      σ ^ n * radialBoundaryJet f r n θ := by
  let L : ℝ →L[ℝ] PolarPoint :=
    (σ • ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)
  let g : PolarPoint → ℝ := fun p => f (p + (r, θ))
  have hpoint : L 0 + (r, θ) = (r, θ) := by rw [L.map_zero, zero_add]
  have hg : ContDiffAt ℝ (n : ℕ∞ω) g (L 0) :=
    (show ContDiffAt ℝ (n : ℕ∞ω) f (L 0 + (r, θ)) by
      rw [hpoint]
      exact hf.of_le (by simp)).comp (L 0) (contDiffAt_id.add contDiffAt_const)
  have he := congrArg (fun A : (ℝ [×n]→L[ℝ] ℝ) => A (fun _ => 1))
    (n06_iteratedFDeriv_compCLM_at L n hg)
  have hslice : g ∘ L = fun x : ℝ => f (rootProfileShift r σ (x, θ)) := by
    funext x
    simp only [Function.comp_apply, g, L, ContinuousLinearMap.prod_apply,
      smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
      smul_eq_mul, rootProfileShift, Prod.mk_add_mk, zero_add, add_zero, add_comm]
  rw [hslice, ContinuousMultilinearMap.compContinuousLinearMap_apply] at he
  have hshift : iteratedFDeriv ℝ n g (L 0) = iteratedFDeriv ℝ n f (r, θ) := by
    change iteratedFDeriv ℝ n (fun p => f (p + (r, θ))) (L 0) = _
    rw [iteratedFDeriv_comp_add_right, hpoint]
  rw [hshift] at he
  have he' : radialBoundaryJet (fun p => f (rootProfileShift r σ p)) 0 n θ =
      iteratedFDeriv ℝ n f (r, θ) (fun _ => (σ, 0)) := by
    simpa only [radialBoundaryJet, iteratedDeriv_eq_iteratedFDeriv, L,
      ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, mul_one] using he
  rw [he', n06_radialBoundaryJet_eq_frechet n hf]
  have hdirs : (fun _ : Fin n => ((σ, 0) : PolarPoint)) =
      fun _ : Fin n => σ • ((1, 0) : PolarPoint) := by
    funext i
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
  rw [hdirs, ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem n04PositiveGeometry_parameter_constMul_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f g : E → ℝ} (Jf : SmoothDirections U f) (Jg : SmoothDirections U g)
    (c : ℝ) (he : EqOn g (fun x => c * f x) U)
    (k : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E) {M : ℝ}
    (hb : ‖Jf.D k x v‖ ≤ M) : ‖Jg.D k x v‖ ≤ |c| * M := by
  let L : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  let Q := (smoothDirections_postcompCLM Jf L).congr
    (fun y hy => (he hy).symm)
  have h := congrArg (fun A : E [×k]→L[ℝ] ℝ => A v) (Jg.unique Q k x hx)
  change Jg.D k x v = (smoothDirections_postcompCLM Jf L).D k x v at h
  rw [smoothDirections_postcompCLM_D_apply] at h
  rw [h]
  simpa only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, norm_mul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left hb (abs_nonneg c)

local instance n04PositiveOrientationDirectionsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}

set_option diagnostics true in
set_option trace.profiler true in
def n04PositiveGeometry_physicalRootTrace_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (π : PolarPoint →L[ℝ] ℝ) (a : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z : (StateDirections S × ℝ) × ℝ => radialBoundaryJet
        (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C z.1) p)) r a z.2) := by
  apply (n04Realization_physicalRootJet_joint hT hS hN hε hr hroot
    π a (fun _ => (1, 0))).congr
  intro z hz
  exact (n06_radialBoundaryJet_eq_frechet a
    (π.contDiff.contDiffAt.comp (r, z.2)
      (n06_physicalRootFields_contDiffAt_root hT hS hN
        (liftSectorParameter_mem_stateNeighborhood hz.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector z.1) hr hroot z.2))).symm

end ContinuousFlexibility.Analysis
