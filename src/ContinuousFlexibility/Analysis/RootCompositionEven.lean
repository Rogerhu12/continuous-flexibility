import ContinuousFlexibility.Analysis.RootCompositionIntegral
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Smooth division in an odd scalar variable

For a smooth function of parameters and one real variable, the integral of
the last partial derivative gives a smooth divided difference.  An odd
function has an even divided difference.  The same construction applied to
the last partial derivative of an even function removes the apparent
singularity in differentiation after a root substitution.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Partial derivative in the parameter variable. -/
def rootParamDerivative (G : E × ℝ → F) (q : E × ℝ) : E →L[ℝ] F :=
  (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- Partial derivative in the last scalar variable. -/
def rootLastDerivative (G : E × ℝ → F) (q : E × ℝ) : F :=
  fderiv ℝ G q (0, 1)

/-- The smooth divided difference from the zero section. -/
def rootDivideLast (G : E × ℝ → F) (q : E × ℝ) : F :=
  ∫ t in (0 : ℝ)..1, rootLastDerivative G (q.1, t * q.2)

theorem contDiff_rootParamDerivative {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (rootParamDerivative G) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_comp contDiff_const

theorem contDiff_rootLastDerivative {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (rootLastDerivative G) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_apply contDiff_const

theorem hasFDerivAt_rootParamDerivative {G : E × ℝ → F}
    (hG : ContDiff ℝ ∞ G) (p : E) (z : ℝ) :
    HasFDerivAt (fun q : E => G (q, z)) (rootParamDerivative G (p, z)) p :=
  ((hG.differentiable (by simp)) (p, z)).hasFDerivAt.comp p
    (hasFDerivAt_prodMk_left p z)

theorem hasDerivAt_rootLastDerivative {G : E × ℝ → F}
    (hG : ContDiff ℝ ∞ G) (p : E) (z : ℝ) :
    HasDerivAt (fun t : ℝ => G (p, t)) (rootLastDerivative G (p, z)) z := by
  exact ((hG.differentiable (by simp)) (p, z)).hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z p).prodMk (hasDerivAt_id' z))

theorem contDiff_rootDivideLast [ProperSpace E] {G : E × ℝ → F}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (rootDivideLast G) := by
  dsimp only [rootDivideLast]
  apply contDiff_intervalIntegral_of_contDiff
  exact (contDiff_rootLastDerivative hG).comp
    (contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd))

/-- The integral divided difference has the expected factorization. -/
theorem rootDivideLast_factor {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G)
    (p : E) (z : ℝ) :
    z • rootDivideLast G (p, z) = G (p, z) - G (p, 0) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => G (p, t * z))
      (z • rootLastDerivative G (p, t * z)) t := by
    simpa only [Function.comp_def] using
      (hasDerivAt_rootLastDerivative hG p (t * z)).scomp t (hasDerivAt_mul_const z)
  have hc : Continuous (fun t : ℝ => z • rootLastDerivative G (p, t * z)) :=
    continuous_const.smul ((contDiff_rootLastDerivative hG).continuous.comp
      (continuous_const.prodMk (continuous_id.mul continuous_const)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simpa only [rootDivideLast, intervalIntegral.integral_smul, one_mul, zero_mul] using h

theorem rootDivideLast_zero (G : E × ℝ → F) (p : E) :
    rootDivideLast G (p, 0) = rootLastDerivative G (p, 0) := by
  simp only [rootDivideLast, mul_zero, intervalIntegral.integral_const, sub_zero, one_smul]

/-- Differentiation in the parameter preserves evenness in the scalar variable. -/
theorem rootParamDerivative_even {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G)
    (he : ∀ p : E, Function.Even (fun z : ℝ => G (p, z))) :
    ∀ p : E, Function.Even (fun z : ℝ => rootParamDerivative G (p, z)) := by
  intro p z
  have hfun : (fun q : E => G (q, -z)) = (fun q : E => G (q, z)) :=
    funext fun q => he q z
  have hm := hasFDerivAt_rootParamDerivative hG p (-z)
  rw [hfun] at hm
  exact hm.unique (hasFDerivAt_rootParamDerivative hG p z)

/-- The scalar derivative of an even function is odd. -/
theorem rootLastDerivative_odd {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G)
    (he : ∀ p : E, Function.Even (fun z : ℝ => G (p, z))) :
    ∀ p : E, Function.Odd (fun z : ℝ => rootLastDerivative G (p, z)) := by
  intro p z
  have hm : HasDerivAt (fun t : ℝ => G (p, -t))
      (-rootLastDerivative G (p, -z)) z := by
    simpa only [Function.comp_def, neg_one_smul] using
      (hasDerivAt_rootLastDerivative hG p (-z)).scomp z (hasDerivAt_neg' (x := z))
  have hfun : (fun t : ℝ => G (p, -t)) = (fun t : ℝ => G (p, t)) :=
    funext fun t => he p t
  rw [hfun] at hm
  have h := congrArg Neg.neg (hm.unique (hasDerivAt_rootLastDerivative hG p z))
  simpa only [neg_neg] using h

/-- Dividing a smooth odd function by its scalar variable gives an even function. -/
theorem rootDivideLast_even {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G)
    (ho : ∀ p : E, Function.Odd (fun z : ℝ => G (p, z))) :
    ∀ p : E, Function.Even (fun z : ℝ => rootDivideLast G (p, z)) := by
  letI : IsAddTorsionFree F := .of_isTorsionFree ℝ F
  intro p z
  by_cases hz : z = 0
  · simp only [hz, neg_zero]
  have hzero : G (p, 0) = 0 := (ho p).map_zero
  have hodd : G (p, -z) = -G (p, z) := ho p z
  have heq : (-z) • rootDivideLast G (p, -z) =
      (-z) • rootDivideLast G (p, z) := by
    rw [rootDivideLast_factor hG, hodd, hzero, sub_zero, neg_smul,
      rootDivideLast_factor hG, hzero, sub_zero]
  have h := congrArg (fun v : F => (-z)⁻¹ • v) heq
  simpa only [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hz), one_smul] using h

end ContinuousFlexibility.Analysis
