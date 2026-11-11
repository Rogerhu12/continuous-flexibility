import ContinuousFlexibility.Analysis.N01cParameterCalculus
import ContinuousFlexibility.Analysis.ProjectiveJetSchwarz
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Actual Fréchet derivatives on finite-dimensional restrictions

A genuine directional tower on a finite-dimensional parameter space gives
ordinary Fréchet smoothness. Joint evaluation continuity supplies operator
norm continuity of each first differential; the existing segment FTC then
proves the Fréchet derivative. Induction yields every order, and uniqueness
identifies the given tower with the actual iterated Fréchet derivatives.

The affine pullback retains the original topological state space. Only its
finite-dimensional parameter space is normed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

section FiniteDimensional

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- Each fixed-direction jet evaluation has the genuine Fréchet
differential supplied by the next directional jet. -/
theorem HasProjectiveJetsOn.hasFDerivAt_eval_finiteDimensional
    {f : X → Y} {J : ProjectiveJetFamily X Y} {U : Set X}
    (hJ : HasProjectiveJetsOn f J U) (hU : IsOpen U)
    (n : ℕ) (v : Fin n → X) {x : X} (hx : x ∈ U) :
    HasFDerivAt (fun y => J n y v) (projectiveJetHeadLinear J n x v) x := by
  have hD : ContinuousOn (fun y => projectiveJetHeadLinear J n y v) U := by
    apply continuousOn_clm_apply.mpr
    intro w
    exact (hJ.continuousOn_headLinear n v).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun y hy => ⟨hy, mem_univ w⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  apply hasFDerivAt_of_continuous_line_differential
    Metric.isOpen_ball (convex_ball x ε) (hD.mono hball) _ (Metric.mem_ball_self hε)
  intro y hy w
  apply hasLineDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [projectiveJetHeadLinear_apply, HasProjectiveLineDerivAt,
    HasProjectiveCurveDerivAt, zero_add, zero_smul, add_zero] using
    hJ.2.2 n y (hball hy) w v

/-- The actual directional recurrence proves all finite smoothness
orders of every fixed-direction jet evaluation. -/
theorem HasProjectiveJetsOn.contDiffOn_eval_finiteDimensional
    {f : X → Y} {J : ProjectiveJetFamily X Y} {U : Set X}
    (hJ : HasProjectiveJetsOn f J U) (hU : IsOpen U)
    (n : ℕ) (v : Fin n → X) :
    ContDiffOn ℝ ∞ (fun x => J n x v) U := by
  have hm : ∀ m : ℕ, ∀ n : ℕ, ∀ v : Fin n → X,
      ContDiffOn ℝ m (fun x => J n x v) U := by
    intro m
    induction m with
    | zero =>
      intro n v
      apply contDiffOn_zero.mpr
      exact (hJ.2.1 n).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx, mem_univ v⟩)
    | succ m ih =>
      intro n v
      have hd (x : X) (hx : x ∈ U) :=
        hJ.hasFDerivAt_eval_finiteDimensional hU n v hx
      have hnext : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) (fun x => J n x v) U := by
        apply contDiffOn_succ_of_fderiv_apply (n := (m : WithTop ℕ∞))
          (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (by simp)
        intro w
        apply (ih (n + 1) (Fin.cons w v)).congr
        intro x hx
        rw [fderivWithin_of_isOpen hU hx, (hd x hx).fderiv,
          projectiveJetHeadLinear_apply]
      simpa only [Nat.cast_add, Nat.cast_one] using hnext
  exact contDiffOn_infty.mpr (fun m => hm m n v)

/-- Genuine directional smoothness on a finite-dimensional open domain
is ordinary Fréchet smoothness. -/
theorem HasProjectiveJetsOn.contDiffOn_finiteDimensional
    {f : X → Y} {J : ProjectiveJetFamily X Y} {U : Set X}
    (hJ : HasProjectiveJetsOn f J U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ f U :=
  (hJ.contDiffOn_eval_finiteDimensional hU 0 Fin.elim0).congr
    (fun x hx => (hJ.1 x hx).symm)

/-- The supplied tower equals the actual Fréchet tower, by uniqueness
of genuine directional derivatives on the same open domain. -/
theorem HasProjectiveJetsOn.eq_iteratedFDeriv_finiteDimensional
    {f : X → Y} {J : ProjectiveJetFamily X Y} {U : Set X}
    (hJ : HasProjectiveJetsOn f J U) (hU : IsOpen U)
    (n : ℕ) {x : X} (hx : x ∈ U) :
    J n x = iteratedFDeriv ℝ n f x :=
  HasProjectiveJetsOn.unique hU hJ
    (hasProjectiveJetsOn_of_contDiffOn hU (hJ.contDiffOn_finiteDimensional hU)) n x hx

theorem smoothDirections_contDiffOn_finiteDimensional
    {f : X → Y} {U : Set X} (J : SmoothDirections U f) :
    ContDiffOn ℝ ∞ f U :=
  J.hasProjectiveJetsOn.contDiffOn_finiteDimensional J.open_domain

end FiniteDimensional

section AffinePullback

variable {E X F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Pull back the genuine tower along an affine map into the original
state space, including the exact multilinear direction formula. -/
def smoothDirections_precompAffine {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (x₀ : E) (L : X →L[ℝ] E) :
    SmoothDirections ((fun y => x₀ + L y) ⁻¹' U) (fun y => f (x₀ + L y)) where
  open_domain := J.open_domain.preimage (continuous_const.add L.continuous)
  D := fun n y => (J.D n (x₀ + L y)).compContinuousLinearMap (fun _ => L)
  zero := by
    intro y hy
    have he : (fun i : Fin 0 => L (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → E) := by
      funext i
      exact i.elim0
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, he]
    exact J.zero (x₀ + L y) hy
  continuous := by
    intro n
    have hmap : Continuous (fun p : X × (Fin n → X) =>
        (x₀ + L p.1, fun i => L (p.2 i))) :=
      (continuous_const.add (L.continuous.comp continuous_fst)).prodMk
        (continuous_pi (fun i => L.continuous.comp
          ((continuous_apply i).comp continuous_snd)))
    exact (J.continuous n).comp hmap.continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  derivative := by
    intro n y hy v w
    have h := J.derivative n (x₀ + L y) hy (fun i => L (v i)) (L w)
    have he : (fun i => L ((Fin.cons w v : Fin (n + 1) → X) i)) =
        (Fin.cons (L w) (fun i => L (v i)) : Fin (n + 1) → E) := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt at h ⊢
    simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply, he,
      map_add, map_smul, ← add_assoc] using h

theorem smoothDirections_precompAffine_D_apply
    {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (x₀ : E) (L : X →L[ℝ] E)
    (n : ℕ) (y : X) (v : Fin n → X) :
    (smoothDirections_precompAffine J x₀ L).D n y v =
      J.D n (x₀ + L y) (fun i => L (v i)) := rfl

end AffinePullback

section FiniteAffinePullback

variable {E X F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem smoothDirections_contDiffOn_finiteAffine
    {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (x₀ : E) (L : X →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun y => f (x₀ + L y)) ((fun y => x₀ + L y) ⁻¹' U) :=
  smoothDirections_contDiffOn_finiteDimensional (smoothDirections_precompAffine J x₀ L)

/-- Finite affine restrictions recover exactly the original continuous
multilinear jets evaluated on the images of the parameter directions. -/
theorem smoothDirections_iteratedFDeriv_finiteAffine
    {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (x₀ : E) (L : X →L[ℝ] E)
    (n : ℕ) {y : X} (hy : x₀ + L y ∈ U) (v : Fin n → X) :
    iteratedFDeriv ℝ n (fun t => f (x₀ + L t)) y v =
      J.D n (x₀ + L y) (fun i => L (v i)) := by
  let K := smoothDirections_precompAffine J x₀ L
  exact congrArg (fun B : X [×n]→L[ℝ] F => B v)
    (K.hasProjectiveJetsOn.eq_iteratedFDeriv_finiteDimensional K.open_domain n hy).symm

end FiniteAffinePullback

end ContinuousFlexibility.Analysis

