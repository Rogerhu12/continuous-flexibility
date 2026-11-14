module

public import ContinuousFlexibility.Contracts.CartesianMetric
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual Euclidean three-dimensional graph embedding

The target is `EuclideanSpace ℝ (Fin 3)`, with its genuine Euclidean inner
product. Smoothness and the topological embedding need no metric hypothesis.
Injectivity of the differential is obtained separately from the actual metric
identity, or from differentiability of the planar inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def e3Basis (i : Fin 3) : E3 := EuclideanSpace.single i 1

def graphMap (P : PolarPoint → PolarPoint) (Z : PolarPoint → ℝ) (x : PolarPoint) : E3 :=
  (P x).1 • e3Basis 0 + (P x).2 • e3Basis 1 + Z x • e3Basis 2

def graphBaseProjection (v : E3) : PolarPoint := (v 0, v 1)

def graphDifferential (L : PolarPoint →L[ℝ] PolarPoint) (M : PolarPoint →L[ℝ] ℝ) :
    PolarPoint →L[ℝ] E3 :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp L).smulRight (e3Basis 0) +
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp L).smulRight (e3Basis 1) +
    M.smulRight (e3Basis 2)

@[simp] theorem graphMap_zero (P : PolarPoint → PolarPoint) (Z : PolarPoint → ℝ)
    (x : PolarPoint) : graphMap P Z x 0 = (P x).1 := by
  simp [graphMap, e3Basis]

@[simp] theorem graphMap_one (P : PolarPoint → PolarPoint) (Z : PolarPoint → ℝ)
    (x : PolarPoint) : graphMap P Z x 1 = (P x).2 := by
  simp [graphMap, e3Basis]

@[simp] theorem graphMap_two (P : PolarPoint → PolarPoint) (Z : PolarPoint → ℝ)
    (x : PolarPoint) : graphMap P Z x 2 = Z x := by
  simp [graphMap, e3Basis]

@[simp] theorem graphBaseProjection_graphMap (P : PolarPoint → PolarPoint)
    (Z : PolarPoint → ℝ) (x : PolarPoint) : graphBaseProjection (graphMap P Z x) = P x := by
  simp [graphBaseProjection]

@[simp] theorem graphDifferential_apply_zero
    (L : PolarPoint →L[ℝ] PolarPoint) (M : PolarPoint →L[ℝ] ℝ) (v : PolarPoint) :
    graphDifferential L M v 0 = (L v).1 := by
  simp [graphDifferential, e3Basis]

@[simp] theorem graphDifferential_apply_one
    (L : PolarPoint →L[ℝ] PolarPoint) (M : PolarPoint →L[ℝ] ℝ) (v : PolarPoint) :
    graphDifferential L M v 1 = (L v).2 := by
  simp [graphDifferential, e3Basis]

@[simp] theorem graphDifferential_apply_two
    (L : PolarPoint →L[ℝ] PolarPoint) (M : PolarPoint →L[ℝ] ℝ) (v : PolarPoint) :
    graphDifferential L M v 2 = M v := by
  simp [graphDifferential, e3Basis]

theorem e3_inner_coordinates (u v : E3) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ]
  ring

theorem continuous_graphBaseProjection : Continuous graphBaseProjection :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.prodMk
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous

theorem continuous_graphMap {P : PolarPoint → PolarPoint} {Z : PolarPoint → ℝ}
    (hP : Continuous P) (hZ : Continuous Z) : Continuous (graphMap P Z) :=
  ((hP.fst.smul continuous_const).add (hP.snd.smul continuous_const)).add
    (hZ.smul continuous_const)

theorem contDiff_graphMap {n : ℕ∞ω} {P : PolarPoint → PolarPoint} {Z : PolarPoint → ℝ}
    (hP : ContDiff ℝ n P) (hZ : ContDiff ℝ n Z) : ContDiff ℝ n (graphMap P Z) :=
  ((hP.fst.smul_const (e3Basis 0)).add (hP.snd.smul_const (e3Basis 1))).add
    (hZ.smul_const (e3Basis 2))

theorem contDiffAt_graphMap {n : ℕ∞ω} {P : PolarPoint → PolarPoint}
    {Z : PolarPoint → ℝ} {x : PolarPoint}
    (hP : ContDiffAt ℝ n P x) (hZ : ContDiffAt ℝ n Z x) :
    ContDiffAt ℝ n (graphMap P Z) x :=
  ((hP.fst.smul_const (e3Basis 0)).add (hP.snd.smul_const (e3Basis 1))).add
    (hZ.smul_const (e3Basis 2))

theorem hasFDerivAt_graphMap {P : PolarPoint → PolarPoint} {Z : PolarPoint → ℝ}
    {L : PolarPoint →L[ℝ] PolarPoint} {M : PolarPoint →L[ℝ] ℝ} {x : PolarPoint}
    (hP : HasFDerivAt P L x) (hZ : HasFDerivAt Z M x) :
    HasFDerivAt (graphMap P Z) (graphDifferential L M) x :=
  ((hP.fst.smul_const (e3Basis 0)).add (hP.snd.smul_const (e3Basis 1))).add
    (hZ.smul_const (e3Basis 2))

theorem fderiv_graphMap {P : PolarPoint → PolarPoint} {Z : PolarPoint → ℝ}
    {x : PolarPoint} (hP : DifferentiableAt ℝ P x) (hZ : DifferentiableAt ℝ Z x) :
    fderiv ℝ (graphMap P Z) x = graphDifferential (fderiv ℝ P x) (fderiv ℝ Z x) :=
  (hasFDerivAt_graphMap hP.hasFDerivAt hZ.hasFDerivAt).fderiv

theorem inner_graphDifferential
    (L : PolarPoint →L[ℝ] PolarPoint) (M : PolarPoint →L[ℝ] ℝ) (u v : PolarPoint) :
    inner ℝ (graphDifferential L M u) (graphDifferential L M v) =
      coordinateEuclideanPair (L u) (L v) + M u * M v := by
  rw [e3_inner_coordinates]
  simp [coordinateEuclideanPair]

theorem isEmbedding_graphMap (P : PolarPoint ≃ₜ PolarPoint) {Z : PolarPoint → ℝ}
    (hZ : Continuous Z) : Topology.IsEmbedding (graphMap P Z) := by
  have hinv : Function.LeftInverse (fun v : E3 => P.symm (graphBaseProjection v)) (graphMap P Z) := by
    intro x
    simp
  exact hinv.isEmbedding (P.symm.continuous.comp continuous_graphBaseProjection)
    (continuous_graphMap P.continuous hZ)

/-- The planar remainder identity gives the actual Euclidean pullback metric of the graph. -/
theorem graphMap_pullback_metric {P : PolarPoint → PolarPoint} {Z : PolarPoint → ℝ}
    {w : ℝ → ℝ} {x : PolarPoint}
    (hP : DifferentiableAt ℝ P x) (hZ : DifferentiableAt ℝ Z x)
    (hmetric : ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) =
        cartesianRemainder w Z x u v) (u v : PolarPoint) :
    inner ℝ (fderiv ℝ (graphMap P Z) x u) (fderiv ℝ (graphMap P Z) x v) =
      cartesianMetric w x u v := by
  rw [fderiv_graphMap hP hZ, inner_graphDifferential, hmetric]
  simp [cartesianRemainder]

theorem graph_cartesianMetric_self_pos (w : ℝ → ℝ) (x : PolarPoint) {v : PolarPoint}
    (hv : v ≠ 0) : 0 < cartesianMetric w x v v := by
  have hq : 0 < coordinateEuclideanPair v v := by
    unfold coordinateEuclideanPair
    by_cases h1 : v.1 = 0
    · have h2 : v.2 ≠ 0 := by
        intro h2
        exact hv (Prod.ext h1 h2)
      nlinarith [sq_pos_of_ne_zero h2]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg v.2]
  have hs := sq_nonneg (cartesianProfileFactor w x * coordinateEuclideanPair x v)
  unfold cartesianMetric
  nlinarith

theorem graphMap_fderiv_injective_of_metric
    {P : PolarPoint → PolarPoint} {Z : PolarPoint → ℝ} {w : ℝ → ℝ} {x : PolarPoint}
    (hP : DifferentiableAt ℝ P x) (hZ : DifferentiableAt ℝ Z x)
    (hmetric : ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) =
        cartesianRemainder w Z x u v) :
    Function.Injective (fderiv ℝ (graphMap P Z) x) := by
  have hker : ∀ v : PolarPoint, fderiv ℝ (graphMap P Z) x v = 0 → v = 0 := by
    intro v hz
    by_contra hv
    have hm := graphMap_pullback_metric hP hZ hmetric v v
    rw [hz, inner_zero_left] at hm
    exact (ne_of_gt (graph_cartesianMetric_self_pos w x hv)) hm.symm
  intro u v huv
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, huv, sub_self]

theorem graphMap_fderiv_injective_of_planar
    {P : PolarPoint → PolarPoint} {Z : PolarPoint → ℝ} {x : PolarPoint}
    (hP : DifferentiableAt ℝ P x) (hZ : DifferentiableAt ℝ Z x)
    (hi : Function.Injective (fderiv ℝ P x)) :
    Function.Injective (fderiv ℝ (graphMap P Z) x) := by
  intro u v huv
  apply hi
  apply Prod.ext
  · simpa [fderiv_graphMap hP hZ] using congrArg (fun y : E3 => y 0) huv
  · simpa [fderiv_graphMap hP hZ] using congrArg (fun y : E3 => y 1) huv

theorem graphMap_fderiv_injective_of_smooth_inverse
    (P : PolarPoint ≃ₜ PolarPoint) {Z : PolarPoint → ℝ} {x : PolarPoint}
    (hP : DifferentiableAt ℝ (P : PolarPoint → PolarPoint) x)
    (hPi : DifferentiableAt ℝ (P.symm : PolarPoint → PolarPoint) (P x))
    (hZ : DifferentiableAt ℝ Z x) :
    Function.Injective (fderiv ℝ (graphMap P Z) x) := by
  have hc := hPi.hasFDerivAt.comp x hP.hasFDerivAt
  have hid : ((P.symm : PolarPoint → PolarPoint) ∘ (P : PolarPoint → PolarPoint)) =
      (id : PolarPoint → PolarPoint) := by funext y; simp
  rw [hid] at hc
  have heq := hc.fderiv
  rw [fderiv_id] at heq
  apply graphMap_fderiv_injective_of_planar hP hZ
  have hleft : Function.LeftInverse (fderiv ℝ (P.symm : PolarPoint → PolarPoint) (P x))
      (fderiv ℝ (P : PolarPoint → PolarPoint) x) := by
    intro v
    simpa using congrArg (fun L : PolarPoint →L[ℝ] PolarPoint => L v) heq.symm
  exact hleft.injective

theorem isEmbedding_graphMap_restrict (P : PolarPoint ≃ₜ PolarPoint)
    {Z : PolarPoint → ℝ} (hZ : Continuous Z) (S : Set PolarPoint) :
    Topology.IsEmbedding (fun x : S => graphMap P Z x) :=
  (isEmbedding_graphMap P hZ).comp Topology.IsEmbedding.subtypeVal

/-- A genuine smooth graph embedding with its induced intrinsic metric and injective
differential. The displayed tensor identity does not assert an ambient distance isometry. -/
theorem graphMap_smooth_embedding_with_metric
    (P : PolarPoint ≃ₜ PolarPoint) {Z : PolarPoint → ℝ} {w : ℝ → ℝ}
    (hP : ContDiff ℝ ∞ (P : PolarPoint → PolarPoint)) (hZ : ContDiff ℝ ∞ Z)
    (hmetric : ∀ x u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ (P : PolarPoint → PolarPoint) x u)
        (fderiv ℝ (P : PolarPoint → PolarPoint) x v) = cartesianRemainder w Z x u v) :
    ContDiff ℝ ∞ (graphMap P Z) ∧ Topology.IsEmbedding (graphMap P Z) ∧
      (∀ x, Function.Injective (fderiv ℝ (graphMap P Z) x)) ∧
      ∀ x u v : PolarPoint,
        inner ℝ (fderiv ℝ (graphMap P Z) x u) (fderiv ℝ (graphMap P Z) x v) =
          cartesianMetric w x u v := by
  refine ⟨contDiff_graphMap hP hZ, isEmbedding_graphMap P hZ.continuous, ?_, ?_⟩
  · intro x
    exact graphMap_fderiv_injective_of_metric (hP.differentiable (by simp) x)
      (hZ.differentiable (by simp) x) (hmetric x)
  · intro x u v
    exact graphMap_pullback_metric (hP.differentiable (by simp) x)
      (hZ.differentiable (by simp) x) (hmetric x) u v

end ContinuousFlexibility
