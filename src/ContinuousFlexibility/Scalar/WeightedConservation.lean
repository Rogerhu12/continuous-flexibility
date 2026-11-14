module

public import ContinuousFlexibility.Statements.ScalarWeighted
public import ContinuousFlexibility.Analysis.MaterialHeightRegularity
public import ContinuousFlexibility.Analysis.ProjectiveJets

/-!
# Conservation and evaluation of weighted scalar towers

A continuous linear conservation functional annihilates every genuine
directional derivative once it annihilates the original map on an open set.
Applying this fact to the physical source functional avoids differentiating
the physical integral separately at every order.  Point evaluation of the
Sobolev decoder is also continuous linear, so the same actual quotient limits
give the pointwise derivative compatibility required by S04.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Analysis

section LinearConservation

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G] [T2Space G]
  {U : Set E} {f : E → F}

/-- A continuous linear conservation law survives every order of an actual
directional tower on its original open domain. -/
theorem SmoothDirections.linear_conservation (J : SmoothDirections U f)
    (L : F →L[ℝ] G) (hzero : ∀ x ∈ U, L (f x) = 0) :
    ∀ k x, x ∈ U → ∀ v : Fin k → E, L (J.D k x v) = 0 := by
  intro k
  induction k with
  | zero =>
      intro x hx v
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv, J.zero x hx]
      exact hzero x hx
  | succ k ih =>
      intro x hx v
      have hd := (J.derivative k x hx (Fin.tail v) (v 0)).clm_comp L
      have hgerm : (fun _ : E => (0 : G)) =ᶠ[𝓝 x]
          (fun y => L (J.D k y (Fin.tail v))) := by
        filter_upwards [J.open_domain.mem_nhds hx] with y hy
        exact (ih y hy (Fin.tail v)).symm
      have hz := (hd.congr_germ hgerm).unique
        (hasProjectiveLineDerivAt_const (0 : G) x (v 0))
      simpa only [Fin.cons_self_tail] using hz

end LinearConservation

section Evaluation

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set E} {f : E → F}

/-- A normed continuous linear output observes the genuine real derivative
along every affine line in the source. -/
theorem SmoothDirections.hasDerivAt_linear_output (J : SmoothDirections U f)
    (L : F →L[ℝ] G) (k : ℕ) (x : E) (hx : x ∈ U)
    (v : Fin k → E) (h : E) :
    HasDerivAt (fun t : ℝ => L (J.D k (x + t • h) v))
      (L (J.D (k + 1) x (Fin.cons h v))) 0 :=
  hasDerivAt_iff_tendsto_slope_zero.mpr ((J.derivative k x hx v h).clm_comp L)

end Evaluation

/-- Point evaluation of the actual Sobolev decoder, with continuity taken
from `IsSobolevModel` rather than postulated for a different decoder. -/
def SobolevModelData.evaluationCLM (M : SobolevModelData)
    (hM : Continuous M.decode) (p : PolarPoint) : M.Space →L[ℝ] ℝ where
  toLinearMap := (LinearMap.proj p).comp M.decode
  cont := (continuous_apply p).comp hM

theorem SobolevModelData.evaluationCLM_apply (M : SobolevModelData)
    (hM : Continuous M.decode) (p : PolarPoint) (u : M.Space) :
    M.evaluationCLM hM p u = M.decode u p := by
  calc
    M.evaluationCLM hM p u = (LinearMap.proj p) (M.decode u) :=
      LinearMap.comp_apply _ _ _
    _ = _ := LinearMap.proj_apply _ _

section PhysicalConservation

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {U : Set E} {f : E → ScalarHeightSpace S}

/-- The conservation, global smoothness, uniform flatness and physical
integral clauses of the S04 tower follow from its zeroth-order conservation. -/
theorem scalarHeightTower_conservation
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (J : SmoothDirections U f) (hzero : ∀ x ∈ U, S.Q (f x) = 0) :
    ∀ k x, x ∈ U → ∀ v : Fin k → E,
      S.Q (J.D k x v) = 0 ∧
      ContDiff ℝ ∞ ((S.height scalarBeta).decode (J.D k x v)) ∧
      UniformFlatJets D ((S.height scalarBeta).decode (J.D k x v)) ∧
      physicalSourceIntegral D ((S.height scalarBeta).decode (J.D k x v)) = 0 := by
  intro k x hx v
  have hz := J.linear_conservation S.Q hzero k x hx v
  obtain ⟨hsmooth, hflat⟩ := physical_height_contDiff_and_flatJets hT hS
    (by norm_num [scalarBeta] : 0 < scalarBeta) (J.D k x v)
  refine ⟨hz, hsmooth, hflat, ?_⟩
  have hQ := hS.2.2.2.2.2.2.2.1 (J.D k x v)
  exact hQ.symm.trans hz

/-- Decoder evaluation commutes with every actual directional derivative.
This is the pointwise compatibility clause in `IsWeightedS04`. -/
theorem scalarHeightTower_decode_derivative
    (hS : IsPhysicalSpaces D T S) (J : SmoothDirections U f)
    (k : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E) (h : E) (p : PolarPoint) :
    HasDerivAt
      (fun t : ℝ => (S.height scalarBeta).decode (J.D k (x + t • h) v) p)
      ((S.height scalarBeta).decode (J.D (k + 1) x (Fin.cons h v)) p) 0 := by
  let L : ScalarHeightSpace S →L[ℝ] ℝ := (S.height scalarBeta).evaluationCLM
    ((hS.1 scalarBeta).2.2.1) p
  simpa only [L, SobolevModelData.evaluationCLM_apply] using
    J.hasDerivAt_linear_output L k x hx v h

end PhysicalConservation

/-- Exact decoding and the scalar conservation law suffice for every
order of the weighted residual tower, on the same chosen state domain. -/
theorem scalarStateResidualTower_conservation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {U : Set (ScalarWeightedState S)} {f : ScalarWeightedState S → ScalarHeightSpace S}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (J : SmoothDirections U f)
    (hdecode : ∀ x ∈ U, ∀ p, (S.height scalarBeta).decode (f x) p =
      scalarStateResidual D S x p)
    (hconservation : ∀ x ∈ U, physicalSourceIntegral D (scalarStateResidual D S x) = 0) :
    ∀ k x, x ∈ U → ∀ v : Fin k → ScalarWeightedState S,
      S.Q (J.D k x v) = 0 ∧
      ContDiff ℝ ∞ ((S.height scalarBeta).decode (J.D k x v)) ∧
      UniformFlatJets D ((S.height scalarBeta).decode (J.D k x v)) ∧
      physicalSourceIntegral D ((S.height scalarBeta).decode (J.D k x v)) = 0 := by
  apply scalarHeightTower_conservation hT hS J
  intro x hx
  have hQ : S.Q (f x) =
      physicalSourceIntegral D ((S.height scalarBeta).decode (f x)) :=
    hS.2.2.2.2.2.2.2.1 (f x)
  have heq : (S.height scalarBeta).decode (f x) = scalarStateResidual D S x :=
    funext (hdecode x hx)
  exact hQ.trans ((congrArg (physicalSourceIntegral D) heq).trans (hconservation x hx))

end ContinuousFlexibility.Statements
