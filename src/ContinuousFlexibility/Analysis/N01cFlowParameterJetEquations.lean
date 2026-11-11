import ContinuousFlexibility.Analysis.N01cFiniteAffineJets
import ContinuousFlexibility.Analysis.N01cFlowFrechetContinuity

/-!
# True time equations for all finite-parameter flow derivatives

Constant directional derivatives commute by the ordinary second
Fréchet derivative theorem. Iterating this identity moves the time
derivative through an arbitrary finite word of parameter directions.
The existing theorem derives joint smoothness from the classical ODE,
so no parameter derivative of the flow is an input here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

section DirectionWords

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def constantDirectionalPartial (d : X) (f : X → Y) : X → Y :=
  fun x => fderiv ℝ f x d

theorem contDiff_constantDirectionalPartial {f : X → Y}
    (hf : ContDiff ℝ ∞ f) (d : X) :
    ContDiff ℝ ∞ (constantDirectionalPartial d f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem constantDirectionalPartial_commute {f : X → Y}
    (hf : ContDiff ℝ ∞ f) (d e : X) :
    constantDirectionalPartial d (constantDirectionalPartial e f) =
      constantDirectionalPartial e (constantDirectionalPartial d f) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ f)).differentiable (by simp)) x
  change fderiv ℝ (fun y => fderiv ℝ f y e) x d =
    fderiv ℝ (fun y => fderiv ℝ f y d) x e
  rw [fderiv_clm_apply hd (differentiableAt_const e),
    fderiv_clm_apply hd (differentiableAt_const d)]
  rw [fderiv_const_apply e, fderiv_const_apply d]
  have hsymm : ((fderiv ℝ (fderiv ℝ f) x) d) e =
      ((fderiv ℝ (fderiv ℝ f) x) e) d :=
    ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq d e
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply] using hsymm

/-- An actual word of constant-direction differential operators. -/
def directionalWord : {n : ℕ} → (Fin n → X) → (X → Y) → X → Y
  | 0, _, f => f
  | n + 1, v, f => constantDirectionalPartial (v 0) (directionalWord (Fin.tail v) f)

theorem contDiff_directionalWord {f : X → Y} (hf : ContDiff ℝ ∞ f)
    {n : ℕ} (v : Fin n → X) :
    ContDiff ℝ ∞ (directionalWord v f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact contDiff_constantDirectionalPartial (ih (Fin.tail v)) (v 0)

theorem constantDirectionalPartial_directionalWord {f : X → Y}
    (hf : ContDiff ℝ ∞ f) (d : X) {n : ℕ} (v : Fin n → X) :
    constantDirectionalPartial d (directionalWord v f) =
      directionalWord v (constantDirectionalPartial d f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change constantDirectionalPartial d
      (constantDirectionalPartial (v 0) (directionalWord (Fin.tail v) f)) = _
    rw [constantDirectionalPartial_commute (contDiff_directionalWord hf (Fin.tail v)),
      ih (Fin.tail v)]
    rfl

theorem directionalWord_eq_iteratedFDeriv {f : X → Y}
    (hf : ContDiff ℝ ∞ f) {n : ℕ} (v : Fin n → X) (x : X) :
    directionalWord v f x = iteratedFDeriv ℝ n f x v := by
  induction n generalizing x with
  | zero => exact (iteratedFDeriv_zero_apply _).symm
  | succ n ih =>
    have he : directionalWord (Fin.tail v) f =
        fun y => iteratedFDeriv ℝ n f y (Fin.tail v) :=
      funext (fun y => ih (Fin.tail v) y)
    change fderiv ℝ (directionalWord (Fin.tail v) f) x (v 0) = _
    rw [he, fderiv_continuousMultilinear_apply_const_apply
      (hf.differentiable_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) x)]
    exact (iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := f) v).symm

end DirectionWords

section ParameterTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exact agreement of the parameter slice derivative with the joint
derivative in directions whose time component is zero. -/
theorem iteratedFDeriv_parameter_slice {F : E × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (q : E) (t : ℝ) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun x => F (x, t)) q v =
      iteratedFDeriv ℝ n F (q, t) (fun i => (v i, 0)) := by
  let J : SmoothDirections (univ : Set (E × ℝ)) F :=
    smoothDirectionsOfJets isOpen_univ (fun k => iteratedFDeriv ℝ k F)
      (hasProjectiveJetsOn_of_contDiffOn isOpen_univ hF.contDiffOn)
  have h := smoothDirections_iteratedFDeriv_finiteAffine J (0, t)
    (ContinuousLinearMap.inl ℝ E ℝ) n (y := q) (mem_univ _) v
  dsimp only [J, smoothDirectionsOfJets] at h
  simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero] using h

/-- Move the true time derivative through any number of actual
parameter Fréchet derivatives. -/
theorem hasDerivAt_iteratedFDeriv_parameter_time {F : E × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (q : E) (t : ℝ) (v : Fin n → E) :
    HasDerivAt (fun r => iteratedFDeriv ℝ n (fun x => F (x, r)) q v)
      (iteratedFDeriv ℝ n
        (fun x => fderiv ℝ F (x, t) (0, 1)) q v) t := by
  let w : Fin n → E × ℝ := fun i => (v i, 0)
  let H : E × ℝ → ℝ := directionalWord w F
  have hH : ContDiff ℝ ∞ H := contDiff_directionalWord hF w
  have he (r : ℝ) :
      iteratedFDeriv ℝ n (fun x => F (x, r)) q v = H (q, r) := by
    rw [iteratedFDeriv_parameter_slice hF]
    exact (directionalWord_eq_iteratedFDeriv hF w (q, r)).symm
  have hsource : (fun r => iteratedFDeriv ℝ n (fun x => F (x, r)) q v) =
      fun r => H (q, r) := funext he
  have htarget : fderiv ℝ H (q, t) (0, 1) =
      iteratedFDeriv ℝ n (fun x => fderiv ℝ F (x, t) (0, 1)) q v := by
    change constantDirectionalPartial (0, 1) (directionalWord w F) (q, t) = _
    rw [constantDirectionalPartial_directionalWord hF,
      directionalWord_eq_iteratedFDeriv (contDiff_constantDirectionalPartial hF (0, 1)),
      ← iteratedFDeriv_parameter_slice (contDiff_constantDirectionalPartial hF (0, 1))]
    rfl
  rw [hsource, ← htarget]
  exact (hH.differentiable (by simp) (q, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t q).prodMk (hasDerivAt_id' t))

end ParameterTime

section GlobalParameterTime

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every actual finite-parameter jet satisfies the differentiated
classical time equation. All parameter regularity is proved from the
given speed and the classical trajectories. -/
theorem globalCircleVectorTrajectory_hasDerivAt_parameterJet_time
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q : E, Θ (q, 0) = θ₀)
    (hflow : ∀ q : E, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    (n : ℕ) (q : E) (t : ℝ) (v : Fin n → E) :
    HasDerivAt (fun r => iteratedFDeriv ℝ n (fun x => Θ (x, r)) q v)
      (iteratedFDeriv ℝ n (fun x => G (x, (t, Θ (x, t)))) q v) t := by
  have hs : ContDiff ℝ ∞ Θ :=
    contDiff_globalCircleVectorTrajectory (E := E) hG hΘ hinit hflow
  have he : (fun x => fderiv ℝ Θ (x, t) (0, 1)) =
      fun x => G (x, (t, Θ (x, t))) := by
    funext x
    have hd : HasDerivAt (fun r => Θ (x, r)) (fderiv ℝ Θ (x, t) (0, 1)) t :=
      (hs.differentiable (by simp) (x, t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk (hasDerivAt_id' t))
    exact hd.unique (hflow x t)
  simpa only [he] using hasDerivAt_iteratedFDeriv_parameter_time hs n q t v

theorem globalCircleVectorTrajectory_parameterJet_initial
    {Θ : E × ℝ → ℝ} {θ₀ : ℝ} (hinit : ∀ q : E, Θ (q, 0) = θ₀)
    (n : ℕ) (q : E) (v : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) (fun x => Θ (x, 0)) q v = 0 := by
  have he : (fun x => Θ (x, 0)) = fun _ => θ₀ := funext hinit
  rw [he, iteratedFDeriv_succ_const]
  rfl

end GlobalParameterTime

end ContinuousFlexibility.Analysis
