import ContinuousFlexibility.Analysis.RootCompositionEven
import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Smooth substitution at a root

An even smooth function of a scalar variable remains smooth on the
nonnegative halfspace after substituting a three-halves power.  The first
derivative is computed using the globally differentiable root power.  Its
apparently singular factor cancels against the odd scalar derivative of
the integrand.  This yields an induction on the smoothness order with
values in arbitrary Banach spaces, including spaces of linear maps.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- At nonnegative parameter values, the root derivative has a polynomial
coefficient after dividing the odd scalar derivative by its scalar variable. -/
theorem hasFDerivAt_even_rootSubstitution
    (L : E →L[ℝ] ℝ) {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G)
    (he : ∀ p : E, Function.Even (fun z : ℝ => G (p, z)))
    (p : E) (hp : 0 ≤ L p) :
    HasFDerivAt (fun q : E => G (q, (L q) ^ (3 / 2 : ℝ)))
      (rootParamDerivative G (p, (L p) ^ (3 / 2 : ℝ)) +
        L.smulRight (((3 / 2 : ℝ) * (L p) ^ 2) •
          rootDivideLast (rootLastDerivative G) (p, (L p) ^ (3 / 2 : ℝ)))) p := by
  letI : IsAddTorsionFree F := .of_isTorsionFree ℝ F
  let r : ℝ := (L p) ^ (3 / 2 : ℝ)
  let a : ℝ := (3 / 2 : ℝ) * (L p) ^ ((3 / 2 : ℝ) - 1)
  let J : E × ℝ → F := rootDivideLast (rootLastDerivative G)
  have hQ := contDiff_rootLastDerivative hG
  have hodd := rootLastDerivative_odd hG he
  have hzero : rootLastDerivative G (p, 0) = 0 := (hodd p).map_zero
  have hfactor : rootLastDerivative G (p, r) = r • J (p, r) := by
    simpa only [J, hzero, sub_zero] using (rootDivideLast_factor hQ p r).symm
  have hpow : (L p) ^ ((3 / 2 : ℝ) - 1) * (L p) ^ (3 / 2 : ℝ) =
      (L p) ^ 2 := by
    rw [← Real.rpow_add' hp (by norm_num : (3 / 2 : ℝ) - 1 + 3 / 2 ≠ 0)]
    norm_num [Real.rpow_two]
  have har : a * r = (3 / 2 : ℝ) * (L p) ^ 2 := by
    dsimp only [a, r]
    rw [mul_assoc, hpow]
  have hr : HasFDerivAt (fun q : E => (L q) ^ (3 / 2 : ℝ)) (a • L) p :=
    L.hasFDerivAt.rpow_const (Or.inr (by norm_num))
  have hc : HasFDerivAt (fun q : E => G (q, (L q) ^ (3 / 2 : ℝ)))
      ((fderiv ℝ G (p, r)).comp ((ContinuousLinearMap.id ℝ E).prod (a • L))) p := by
    simpa only [Function.comp_def, id] using
      ((hG.differentiable (by simp)) (p, r)).hasFDerivAt.comp p
        ((hasFDerivAt_id p).prodMk hr)
  apply hc.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    rootParamDerivative, ContinuousLinearMap.inl_apply, smul_eq_mul]
  have hv : (v, a * L v) = (v, (0 : ℝ)) + (a * L v) • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul]
  change fderiv ℝ G (p, r) (v, 0) + (a * L v) • rootLastDerivative G (p, r) = _
  rw [hfactor]
  congr 1
  rw [smul_smul, smul_smul]
  have heq : a * L v * r = L v * ((3 / 2 : ℝ) * (L p) ^ 2) := by
    calc
      a * L v * r = (a * r) * L v := by ring
      _ = L v * ((3 / 2 : ℝ) * (L p) ^ 2) := by rw [har, mul_comm]
  rw [heq]

private theorem contDiffOn_nat_even_rootSubstitution
    (n : ℕ) (L : E →L[ℝ] ℝ) (S : Set E) (hS : UniqueDiffOn ℝ S)
    (hpos : ∀ p ∈ S, 0 ≤ L p) :
    ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      {G : E × ℝ → V}, ContDiff ℝ ∞ G →
      (∀ p : E, Function.Even (fun z : ℝ => G (p, z))) →
      ContDiffOn ℝ n (fun p : E => G (p, (L p) ^ (3 / 2 : ℝ))) S := by
  induction n with
  | zero =>
      intro V _ _ _ G hG _
      apply contDiffOn_zero.mpr
      exact (hG.continuous.comp (continuous_id.prodMk
        ((Real.continuous_rpow_const (by norm_num : 0 ≤ (3 / 2 : ℝ))).comp
          L.continuous))).continuousOn
  | succ n ih =>
      intro V _ _ _ G hG he
      let J : E × ℝ → V := rootDivideLast (rootLastDerivative G)
      have hJ : ContDiff ℝ ∞ J := contDiff_rootDivideLast (contDiff_rootLastDerivative hG)
      have heJ : ∀ p : E, Function.Even (fun z : ℝ => J (p, z)) :=
        rootDivideLast_even (contDiff_rootLastDerivative hG) (rootLastDerivative_odd hG he)
      have hP : ContDiffOn ℝ n
          (fun p : E => rootParamDerivative G (p, (L p) ^ (3 / 2 : ℝ))) S :=
        ih (contDiff_rootParamDerivative hG) (rootParamDerivative_even hG he)
      have hQ : ContDiffOn ℝ n
          (fun p : E => J (p, (L p) ^ (3 / 2 : ℝ))) S := ih hJ heJ
      have hcoeff : ContDiffOn ℝ n (fun p : E => (3 / 2 : ℝ) * (L p) ^ 2) S :=
        contDiffOn_const.mul (L.contDiff.contDiffOn.pow 2)
      have hnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1)
          (fun p : E => G (p, (L p) ^ (3 / 2 : ℝ))) S := by
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS).mpr
        refine ⟨by simp, ?_⟩
        refine ⟨fun p => rootParamDerivative G (p, (L p) ^ (3 / 2 : ℝ)) +
          L.smulRight (((3 / 2 : ℝ) * (L p) ^ 2) • J (p, (L p) ^ (3 / 2 : ℝ))),
          hP.add (contDiffOn_const.smulRight (hcoeff.smul hQ)), ?_⟩
        intro p hp
        exact (hasFDerivAt_even_rootSubstitution L hG he p (hpos p hp)).hasFDerivWithinAt
      simpa only [Nat.cast_add, Nat.cast_one] using hnext

/-- Smooth even scalar dependence removes the singularity of the root
substitution, including at the boundary of any nonnegative parameter set. -/
theorem contDiffOn_even_rootSubstitution
    (L : E →L[ℝ] ℝ) {S : Set E} (hS : UniqueDiffOn ℝ S)
    (hpos : ∀ p ∈ S, 0 ≤ L p) {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G)
    (he : ∀ p : E, Function.Even (fun z : ℝ => G (p, z))) :
    ContDiffOn ℝ ∞ (fun p : E => G (p, (L p) ^ (3 / 2 : ℝ))) S := by
  apply contDiffOn_infty.mpr
  intro n
  exact contDiffOn_nat_even_rootSubstitution n L S hS hpos hG he

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

/-- The even root substitution is smooth up to the nonnegative boundary. -/
theorem contDiffOn_rootEven {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiffOn ℝ ∞ (rootEven G) (Ici (0 : ℝ) ×ˢ univ) := by
  let H : PolarPoint × ℝ → ℝ := fun q => G (q.1.1, q.2, q.1.2)
  have hH : ContDiff ℝ ∞ H :=
    hG.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd))
  let K : PolarPoint × ℝ → ℝ := fun q => (H q + H (q.1, -q.2)) / 2
  have hK : ContDiff ℝ ∞ K :=
    (hH.add (hH.comp (contDiff_fst.prodMk contDiff_snd.neg))).div_const 2
  have heK : ∀ p : PolarPoint, Function.Even (fun z : ℝ => K (p, z)) := by
    intro p z
    dsimp only [K]
    rw [neg_neg, add_comm]
  have h := contDiffOn_even_rootSubstitution (ContinuousLinearMap.fst ℝ ℝ ℝ)
    ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ)
    (fun p hp => by simpa only [ContinuousLinearMap.coe_fst', mem_Ici] using hp.1) hK heK
  unfold rootEven
  simpa only [ContinuousLinearMap.coe_fst', K, H] using h

/-- The prescribed odd quotient has a smooth extension within the
nonnegative halfspace, including its derivative value on the zero section. -/
theorem contDiffOn_rootOdd {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiffOn ℝ ∞ (rootOdd G) (Ici (0 : ℝ) ×ˢ univ) := by
  let H : PolarPoint × ℝ → ℝ := fun q => G (q.1.1, q.2, q.1.2)
  have hH : ContDiff ℝ ∞ H :=
    hG.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd))
  let O : PolarPoint × ℝ → ℝ := fun q => (H q - H (q.1, -q.2)) / 2
  have hO : ContDiff ℝ ∞ O :=
    (hH.sub (hH.comp (contDiff_fst.prodMk contDiff_snd.neg))).div_const 2
  have hoO : ∀ p : PolarPoint, Function.Odd (fun z : ℝ => O (p, z)) := by
    intro p z
    dsimp only [O]
    rw [neg_neg]
    ring
  let Q : PolarPoint × ℝ → ℝ := rootDivideLast O
  have hQ : ContDiff ℝ ∞ Q := contDiff_rootDivideLast hO
  have heQ : ∀ p : PolarPoint, Function.Even (fun z : ℝ => Q (p, z)) :=
    rootDivideLast_even hO hoO
  have hsmooth : ContDiffOn ℝ ∞
      (fun p : PolarPoint => Q (p, p.1 ^ (3 / 2 : ℝ))) (Ici (0 : ℝ) ×ˢ univ) := by
    simpa only [ContinuousLinearMap.coe_fst'] using
      contDiffOn_even_rootSubstitution (ContinuousLinearMap.fst ℝ ℝ ℝ)
        ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ)
        (fun p hp => by simpa only [ContinuousLinearMap.coe_fst', mem_Ici] using hp.1) hQ heQ
  apply hsmooth.congr
  intro p hp
  by_cases hx : p.1 = 0
  · let d : ℝ := rootLastDerivative H (p, 0)
    have hd : HasDerivAt (fun t : ℝ => H (p, t)) d 0 :=
      hasDerivAt_rootLastDerivative hH p 0
    have hdm : HasDerivAt (fun t : ℝ => H (p, -t)) (-d) 0 := by
      simpa only [Function.comp_def, neg_zero, neg_one_smul, d] using
        (hasDerivAt_rootLastDerivative hH p (-(0 : ℝ))).scomp 0
          (hasDerivAt_neg' (x := (0 : ℝ)))
    have hOd : HasDerivAt (fun t : ℝ => O (p, t)) d 0 :=
      ((hd.fun_sub hdm).div_const 2).congr_deriv (by ring)
    have hQzero : Q (p, 0) = d := by
      exact (rootDivideLast_zero O p).trans
        ((hasDerivAt_rootLastDerivative hO p 0).unique hOd)
    have horiginal : deriv (fun t : ℝ => G (0, t, p.2)) 0 = d := by
      simpa only [H, hx] using hd.deriv
    have hrzero : p.1 ^ (3 / 2 : ℝ) = 0 := by
      rw [hx, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    rw [rootOdd, if_pos hx, hrzero, hQzero]
    exact horiginal
  · have hxpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hx)
    have hrne : p.1 ^ (3 / 2 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hxpos _).ne'
    have hfactor : p.1 ^ (3 / 2 : ℝ) * Q (p, p.1 ^ (3 / 2 : ℝ)) =
        (G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) -
          G (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2)) / 2 := by
      simpa only [Q, O, H, neg_zero, sub_self, zero_div, sub_zero, smul_eq_mul] using
        rootDivideLast_factor hO p (p.1 ^ (3 / 2 : ℝ))
    rw [rootOdd, if_neg hx]
    apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hrne)).mpr
    nlinarith only [hfactor]

end ContinuousFlexibility.Statements
