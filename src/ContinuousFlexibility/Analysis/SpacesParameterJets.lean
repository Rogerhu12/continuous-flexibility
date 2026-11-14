module

public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Parameter differentiation of smooth spatial jets

Constant directional partials commute for smooth functions. Applying that
fact to the parameter, radial, and angular directions proves the actual
parameter derivative formula for every mixed spatial jet.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

section Directional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spacesDirectionalPartial (d : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x d

theorem spacesDirectionalPartial_contDiff {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (d : E) :
    ContDiff ℝ ∞ (spacesDirectionalPartial d f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem spacesDirectionalPartial_iterate_contDiff {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (d : E) (n : ℕ) : ContDiff ℝ ∞ ((spacesDirectionalPartial d)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact spacesDirectionalPartial_contDiff ih d

theorem spacesDirectionalPartial_commute {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (d e : E) :
    spacesDirectionalPartial d (spacesDirectionalPartial e f) =
      spacesDirectionalPartial e (spacesDirectionalPartial d f) := by
  funext x
  have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt.of_le (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heval (u v : E) : fderiv ℝ (fun y => fderiv ℝ f y u) x v =
      fderiv ℝ (fderiv ℝ f) x v u := by
    rw [fderiv_clm_apply hd (differentiableAt_const u)]
    simp
  unfold spacesDirectionalPartial
  rw [heval, heval]
  exact (h2.isSymmSndFDerivAt (by norm_num)) d e

theorem spacesDirectionalPartial_iterate_commute {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (d e : E) (n : ℕ) :
    spacesDirectionalPartial d ((spacesDirectionalPartial e)^[n] f) =
      (spacesDirectionalPartial e)^[n] (spacesDirectionalPartial d f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',
      spacesDirectionalPartial_commute (spacesDirectionalPartial_iterate_contDiff hf e n) d e,
      ih, Function.iterate_succ_apply']

theorem spaces_iteratedDeriv_directional_slice {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (σ : ℝ → E) (d : E) (hσ : ∀ t, HasDerivAt σ d t) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun s => f (σ s)) t = (spacesDirectionalPartial d)^[n] f (σ t) := by
  induction n generalizing t with
  | zero => simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq]
  | succ n ih =>
    have he : iteratedDeriv n (fun s => f (σ s)) =
        fun s => (spacesDirectionalPartial d)^[n] f (σ s) := funext ih
    have hd := ((spacesDirectionalPartial_iterate_contDiff hf d n).differentiable
      (by simp) (σ t)).hasFDerivAt.comp_hasDerivAt t (hσ t)
    rw [iteratedDeriv_succ, he, Function.iterate_succ_apply']
    exact hd.deriv

end Directional

private def spacesParameterDirection : ℝ × PolarPoint := (1, (0, 0))
private def spacesParameterRadialDirection : ℝ × PolarPoint := (0, (1, 0))
private def spacesParameterAngularDirection : ℝ × PolarPoint := (0, (0, 1))

def spacesParameterMixedIterates (f : ℝ × PolarPoint → ℝ) (a b : ℕ) : ℝ × PolarPoint → ℝ :=
  (spacesDirectionalPartial spacesParameterRadialDirection)^[a]
    ((spacesDirectionalPartial spacesParameterAngularDirection)^[b] f)

theorem spacesParameterMixedIterates_contDiff {f : ℝ × PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b : ℕ) : ContDiff ℝ ∞ (spacesParameterMixedIterates f a b) :=
  spacesDirectionalPartial_iterate_contDiff
    (spacesDirectionalPartial_iterate_contDiff hf spacesParameterAngularDirection b)
    spacesParameterRadialDirection a

theorem spacesParameterMixedIterates_eq {f : ℝ × PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b : ℕ) (t : ℝ) (p : PolarPoint) :
    spacesParameterMixedIterates f a b (t, p) =
      mixedDerivative a b (fun q => f (t, q)) p := by
  have hθ (r θ : ℝ) : iteratedDeriv b (fun y : ℝ => f (t, (r, y))) θ =
      (spacesDirectionalPartial spacesParameterAngularDirection)^[b] f (t, (r, θ)) := by
    exact spaces_iteratedDeriv_directional_slice hf (fun y => (t, (r, y)))
      spacesParameterAngularDirection
      (fun y => (hasDerivAt_const y t).prodMk
        ((hasDerivAt_const y r).prodMk (hasDerivAt_id' y))) b θ
  unfold mixedDerivative
  simp_rw [hθ]
  exact (spaces_iteratedDeriv_directional_slice
    (spacesDirectionalPartial_iterate_contDiff hf spacesParameterAngularDirection b)
    (fun r => (t, (r, p.2))) spacesParameterRadialDirection
    (fun r => (hasDerivAt_const r t).prodMk
      ((hasDerivAt_id' r).prodMk (hasDerivAt_const r p.2))) a p.1).symm

/-- The mixed spatial jets are jointly smooth in the real parameter and point. -/
theorem spaces_contDiff_parameter_mixedDerivative {f : ℝ × PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b : ℕ) :
    ContDiff ℝ ∞ (fun z : ℝ × PolarPoint => mixedDerivative a b (fun p => f (z.1, p)) z.2) := by
  have he : (fun z : ℝ × PolarPoint => mixedDerivative a b (fun p => f (z.1, p)) z.2) =
      spacesParameterMixedIterates f a b := by
    funext z
    exact (spacesParameterMixedIterates_eq hf a b z.1 z.2).symm
  rw [he]
  exact spacesParameterMixedIterates_contDiff hf a b

/-- Real parameter differentiation commutes with every mixed spatial jet. -/
theorem spaces_hasDerivAt_parameter_mixedDerivative {f : ℝ × PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b : ℕ) (t : ℝ) (p : PolarPoint) :
    HasDerivAt (fun s => mixedDerivative a b (fun q => f (s, q)) p)
      (mixedDerivative a b (fun q => deriv (fun s => f (s, q)) t) p) t := by
  have hs (s : ℝ) : HasDerivAt (fun r : ℝ => (r, p)) spacesParameterDirection s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s p)
  have hd := ((spacesParameterMixedIterates_contDiff hf a b).differentiable
    (by simp) (t, p)).hasFDerivAt.comp_hasDerivAt t (hs t)
  have hcurve : (fun s => spacesParameterMixedIterates f a b (s, p)) =
      fun s => mixedDerivative a b (fun q => f (s, q)) p :=
    funext (fun s => spacesParameterMixedIterates_eq hf a b s p)
  change HasDerivAt (fun s => spacesParameterMixedIterates f a b (s, p))
    (spacesDirectionalPartial spacesParameterDirection (spacesParameterMixedIterates f a b) (t, p)) t at hd
  rw [hcurve] at hd
  have hcomm : spacesDirectionalPartial spacesParameterDirection (spacesParameterMixedIterates f a b) =
      spacesParameterMixedIterates (spacesDirectionalPartial spacesParameterDirection f) a b := by
    unfold spacesParameterMixedIterates
    rw [spacesDirectionalPartial_iterate_commute
      (spacesDirectionalPartial_iterate_contDiff hf spacesParameterAngularDirection b),
      spacesDirectionalPartial_iterate_commute hf]
  rw [hcomm, spacesParameterMixedIterates_eq (spacesDirectionalPartial_contDiff hf _) a b] at hd
  have hpder : (fun q => spacesDirectionalPartial spacesParameterDirection f (t, q)) =
      fun q => deriv (fun s => f (s, q)) t := by
    funext q
    have hq := (hf.differentiable (by simp) (t, q)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id' t).prodMk (hasDerivAt_const t q))
    exact hq.deriv.symm
  rwa [hpder] at hd

end ContinuousFlexibility.Statements
