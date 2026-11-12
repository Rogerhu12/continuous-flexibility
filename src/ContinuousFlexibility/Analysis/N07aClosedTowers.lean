import ContinuousFlexibility.Analysis.SolveTameSubspace
import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Genuine parameter towers in closed graph spaces

Only the original values need to be identified in the closed graph.
Every higher directional derivative then lies in the same graph by the
actual difference quotient. This avoids assuming interchange of spatial
and parameter derivatives when passing through the Sobolev realization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]

/-- A genuine tower whose original values have a representative in a
closed linear subspace lifts to that actual representative. -/
def n07aSmoothDirectionsCodRestrict
    (W : Submodule ℝ Y) (hW : IsClosed (W : Set Y))
    {U : Set X} {f : X → Y} (J : SmoothDirections U f)
    (g : X → W) (hg : ∀ x ∈ U, (g x : Y) = f x) : SmoothDirections U g := by
  classical
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
    rw [dite_eq_left hx]
    exact ContinuousMultilinearMap.codRestrict_apply_coe _ _ _ _
  exact
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

theorem n07aSmoothDirectionsCodRestrict_D_coe
    (W : Submodule ℝ Y) (hW : IsClosed (W : Set Y))
    {U : Set X} {f : X → Y} (J : SmoothDirections U f)
    (g : X → W) (hg : ∀ x ∈ U, (g x : Y) = f x)
    (n : ℕ) {x : X} (hx : x ∈ U) (v : Fin n → X) :
    ((n07aSmoothDirectionsCodRestrict W hW J g hg).D n x v : Y) = J.D n x v := by
  classical
  dsimp only [n07aSmoothDirectionsCodRestrict]
  rw [dite_eq_left hx]
  exact ContinuousMultilinearMap.codRestrict_apply_coe _ _ _ _

section Projective

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  {bond : ∀ n, E (n + 1) →L[ℝ] E n}
  {U : Set X} {f : ∀ n, X → E n}

/-- Coordinate towers lift through the actual closed compatibility graph
once their zeroth values agree with an actual projective element. -/
def n07aSmoothDirectionsProjective (hU : IsOpen U)
    (J : ∀ n, SmoothDirections U (f n))
    (g : X → ProjectiveLimit E bond)
    (hg : ∀ x ∈ U, ∀ n, (g x).val n = f n x) : SmoothDirections U g :=
  n07aSmoothDirectionsCodRestrict (compatibleSubmodule E bond)
    (isClosed_compatibleSubmodule E bond) (smoothDirectionsScalarPi hU J) g
    (fun x hx => funext (hg x hx))

theorem n07aSmoothDirectionsProjective_D_coordinate (hU : IsOpen U)
    (J : ∀ n, SmoothDirections U (f n))
    (g : X → ProjectiveLimit E bond)
    (hg : ∀ x ∈ U, ∀ n, (g x).val n = f n x)
    (k : ℕ) {x : X} (hx : x ∈ U) (v : Fin k → X) (n : ℕ) :
    ((n07aSmoothDirectionsProjective hU J g hg).D k x v).val n = (J n).D k x v := by
  have h := n07aSmoothDirectionsCodRestrict_D_coe (compatibleSubmodule E bond)
    (isClosed_compatibleSubmodule E bond) (smoothDirectionsScalarPi hU J) g
    (fun x hx => funext (hg x hx)) k hx v
  exact congrArg (fun u : ∀ n, E n => u n) h

end Projective

end ContinuousFlexibility.Analysis
