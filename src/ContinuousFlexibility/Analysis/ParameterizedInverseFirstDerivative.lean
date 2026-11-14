module

public import ContinuousFlexibility.Analysis.ParameterizedCircleInverse

/-!
# The actual first differential of a scalar family inverse

External parameters are retained as coordinates. Differentiating the
true right-inverse equation controls the inverse differential by the
original first differential and the original angular lower bound. The
parameter space can contain both independent root parameters.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def scalarFamilyLift (f : P × ℝ → ℝ) (x : P × ℝ) : P × ℝ :=
  (x.1, f x)

theorem scalarRightInverse_fderiv_norm_le
    {f g : P × ℝ → ℝ} {x : P × ℝ} {κ M : ℝ}
    (hf : DifferentiableAt ℝ f (x.1, g x))
    (hg : DifferentiableAt ℝ g x)
    (hright : ∀ y : P × ℝ, f (y.1, g y) = y.2)
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (hangle : κ ≤ fderiv ℝ f (x.1, g x) (0, 1))
    (hbound : ‖fderiv ℝ f (x.1, g x)‖ ≤ M) :
    ‖fderiv ℝ g x‖ ≤ (1 + M) / κ := by
  let D : (P × ℝ) →L[ℝ] ℝ := fderiv ℝ f (x.1, g x)
  let G : (P × ℝ) →L[ℝ] ℝ := fderiv ℝ g x
  have hmap : HasFDerivAt (fun y : P × ℝ => (y.1, g y))
      ((ContinuousLinearMap.fst ℝ P ℝ).prod G) x :=
    hasFDerivAt_fst.prodMk hg.hasFDerivAt
  have hc := hf.hasFDerivAt.comp x hmap
  have he : f ∘ (fun y : P × ℝ => (y.1, g y)) = Prod.snd :=
    funext hright
  rw [he] at hc
  have hsnd : HasFDerivAt (fun y : P × ℝ => y.2)
      (ContinuousLinearMap.snd ℝ P ℝ) x := hasFDerivAt_snd
  have hd := hc.unique hsnd
  have hpos : 0 < D (0, 1) := hκ.trans_le hangle
  have hscale : 0 ≤ (1 + M) / κ := div_nonneg (by linarith) hκ.le
  apply ContinuousLinearMap.opNorm_le_bound _ hscale
  intro v
  have hv := congrArg (fun L : (P × ℝ) →L[ℝ] ℝ => L v) hd
  have hv' : D (v.1, G v) = v.2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', D, G] using hv
  have hsplit : (v.1, G v) = (v.1, (0 : ℝ)) + G v • ((0 : P), (1 : ℝ)) := by
    ext <;> simp
  have hvalue : G v = (v.2 - D (v.1, 0)) / D (0, 1) := by
    apply (eq_div_iff hpos.ne').mpr
    rw [hsplit, map_add, map_smul, smul_eq_mul] at hv'
    linarith only [hv']
  have hparam : ‖(v.1, (0 : ℝ))‖ ≤ ‖v‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v.1)]
    exact norm_fst_le v
  have hlinear : |D (v.1, 0)| ≤ M * ‖v‖ := by
    calc
      _ = ‖D (v.1, 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖D‖ * ‖(v.1, (0 : ℝ))‖ := D.le_opNorm _
      _ ≤ M * ‖v‖ := mul_le_mul hbound hparam (norm_nonneg _) hM
  have hnum : |v.2 - D (v.1, 0)| ≤ (1 + M) * ‖v‖ := by
    calc
      _ ≤ |v.2| + |D (v.1, 0)| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le v.2 (D (v.1, 0))
      _ ≤ ‖v‖ + M * ‖v‖ := add_le_add
        (by simpa only [Real.norm_eq_abs] using norm_snd_le v) hlinear
      _ = _ := by ring
  have hcoeff : 1 + M ≤ ((1 + M) / κ) * D (0, 1) := by
    calc
      _ = ((1 + M) / κ) * κ := (div_mul_cancel₀ _ hκ.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hangle hscale
  change ‖G v‖ ≤ ((1 + M) / κ) * ‖v‖
  rw [Real.norm_eq_abs, hvalue, abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  exact hnum.trans (by
    simpa only [mul_assoc, mul_comm ‖v‖] using
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg v))

theorem scalarFamilyLift_fderiv_norm_le
    {g : P × ℝ → ℝ} {x : P × ℝ} {M : ℝ}
    (hg : DifferentiableAt ℝ g x) (hM : 0 ≤ M)
    (hbound : ‖fderiv ℝ g x‖ ≤ M) :
    ‖fderiv ℝ (scalarFamilyLift g) x‖ ≤ 1 + M := by
  have hd : HasFDerivAt (scalarFamilyLift g)
      ((ContinuousLinearMap.fst ℝ P ℝ).prod (fderiv ℝ g x)) x :=
    hasFDerivAt_fst.prodMk hg.hasFDerivAt
  rw [hd.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro v
  rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', Prod.norm_def]
  apply max_le
  · calc
      ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
      _ ≤ (1 + M) * ‖v‖ := by nlinarith [norm_nonneg v]
  · calc
      ‖fderiv ℝ g x v‖ ≤ ‖fderiv ℝ g x‖ * ‖v‖ := (fderiv ℝ g x).le_opNorm v
      _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg v)
      _ ≤ (1 + M) * ‖v‖ := by nlinarith [norm_nonneg v]

theorem parameterizedCircleInverse_lift_fderiv_norm_le
    [CompleteSpace P] {f : P × ℝ → ℝ} {T κ M : ℝ}
    (hT : T ≠ 0) (hf : ContDiff ℝ ∞ f)
    (hpositive : ∀ y : P × ℝ, 0 < deriv (fun θ => f (y.1, θ)) y.2)
    (hperiod : ∀ p θ, f (p, θ + T) = f (p, θ) + T)
    (x : P × ℝ) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hangle : κ ≤ deriv (fun θ => f (x.1, θ)) (parameterizedCircleInverse f x))
    (hbound : ‖fderiv ℝ f (x.1, parameterizedCircleInverse f x)‖ ≤ M) :
    ‖fderiv ℝ (scalarFamilyLift (parameterizedCircleInverse f)) x‖ ≤
      1 + (1 + M) / κ := by
  let g : P × ℝ → ℝ := parameterizedCircleInverse f
  have hg : ContDiff ℝ ∞ g :=
    contDiff_parameterizedCircleInverse hT hf hpositive hperiod
  have hd : DifferentiableAt ℝ f (x.1, g x) := hf.differentiable (by simp) _
  have hline : HasDerivAt (fun θ : ℝ => (x.1, θ)) ((0 : P), 1) (g x) :=
    (hasDerivAt_const (g x) x.1).prodMk (hasDerivAt_id (g x))
  have hc := hd.hasFDerivAt.comp_hasDerivAt (g x) hline
  have he : fderiv ℝ f (x.1, g x) (0, 1) =
      deriv (fun θ => f (x.1, θ)) (g x) := by
    simpa only [Function.comp_def] using hc.deriv.symm
  have hb : ‖fderiv ℝ g x‖ ≤ (1 + M) / κ :=
    scalarRightInverse_fderiv_norm_le hd (hg.differentiable (by simp) x)
      (parameterizedCircleInverse_right_inverse hT hf hperiod) hκ hM
      (he.symm ▸ hangle) hbound
  exact scalarFamilyLift_fderiv_norm_le (hg.differentiable (by simp) x)
    (div_nonneg (by linarith) hκ.le) hb

end ContinuousFlexibility.Analysis
