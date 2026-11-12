import ContinuousFlexibility.Analysis.N07aNormalRecurrence
import ContinuousFlexibility.Analysis.N07bInteriorGreen
import ContinuousFlexibility.Scalar.WeightedPartialIdentities

/-!
# The physical divergence equation in one genuine local chart

The coefficients below are computed from the physical coefficients and
the forward coordinate map. Both sides of a moving cut can therefore use
the same smooth coefficients after pullback by one local inverse. No
regularity or transformed equation for the solution is built into them.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

/-- The principal quadratic form evaluated on the two coordinate covectors. -/
def n07aPullbackPrincipal (L : SymmetricCoefficients)
    (F : PolarPoint → PolarPoint) : SymmetricCoefficients where
  a x := L.a x * radialPartial (fun q => (F q).1) x ^ 2 +
    2 * L.b x * radialPartial (fun q => (F q).1) x *
      angularPartial (fun q => (F q).1) x +
    L.c x * angularPartial (fun q => (F q).1) x ^ 2
  b x := L.a x * radialPartial (fun q => (F q).1) x *
      radialPartial (fun q => (F q).2) x +
    L.b x * (radialPartial (fun q => (F q).1) x *
      angularPartial (fun q => (F q).2) x +
      angularPartial (fun q => (F q).1) x * radialPartial (fun q => (F q).2) x) +
    L.c x * angularPartial (fun q => (F q).1) x *
      angularPartial (fun q => (F q).2) x
  c x := L.a x * radialPartial (fun q => (F q).2) x ^ 2 +
    2 * L.b x * radialPartial (fun q => (F q).2) x *
      angularPartial (fun q => (F q).2) x +
    L.c x * angularPartial (fun q => (F q).2) x ^ 2

/-- Normalized coefficients, in the order used by `n07aNormalRhs`. -/
def n07aPullbackNormalCoefficients (L : SymmetricCoefficients)
    (F G : PolarPoint → PolarPoint) : Fin 6 → PolarPoint → ℝ :=
  ![fun y => -2 * (n07aPullbackPrincipal L F).b (G y) /
      (n07aPullbackPrincipal L F).a (G y),
    fun y => -(n07aPullbackPrincipal L F).c (G y) /
      (n07aPullbackPrincipal L F).a (G y),
    fun y => -divergenceOperator L (fun x => (F x).1) (G y) /
      (n07aPullbackPrincipal L F).a (G y),
    fun y => -divergenceOperator L (fun x => (F x).2) (G y) /
      (n07aPullbackPrincipal L F).a (G y),
    fun _ => 0,
    fun y => ((n07aPullbackPrincipal L F).a (G y))⁻¹]

theorem n07a_localPullback_radial_smooth {U : Set PolarPoint} (hU : IsOpen U)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (radialPartial f) U :=
  fun x hx => (contDiffAt_radialPartial (hf.contDiffAt (hU.mem_nhds hx))
    (by simp)).contDiffWithinAt

theorem n07a_localPullback_angular_smooth {U : Set PolarPoint} (hU : IsOpen U)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (angularPartial f) U :=
  fun x hx => (contDiffAt_angularPartial (hf.contDiffAt (hU.mem_nhds hx))
    (by simp)).contDiffWithinAt

theorem n07a_localPullback_principal_contDiffAt
    {L : SymmetricCoefficients} {F : PolarPoint → PolarPoint} {x : PolarPoint}
    (ha : ContDiffAt ℝ ∞ L.a x) (hb : ContDiffAt ℝ ∞ L.b x)
    (hc : ContDiffAt ℝ ∞ L.c x) (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (n07aPullbackPrincipal L F).a x ∧
      ContDiffAt ℝ ∞ (n07aPullbackPrincipal L F).b x ∧
      ContDiffAt ℝ ∞ (n07aPullbackPrincipal L F).c x := by
  have hrr : ContDiffAt ℝ ∞ (radialPartial (fun q => (F q).1)) x :=
    contDiffAt_radialPartial hF.fst (by simp)
  have htr : ContDiffAt ℝ ∞ (angularPartial (fun q => (F q).1)) x :=
    contDiffAt_angularPartial hF.fst (by simp)
  have hrt : ContDiffAt ℝ ∞ (radialPartial (fun q => (F q).2)) x :=
    contDiffAt_radialPartial hF.snd (by simp)
  have htt : ContDiffAt ℝ ∞ (angularPartial (fun q => (F q).2)) x :=
    contDiffAt_angularPartial hF.snd (by simp)
  exact ⟨((ha.mul (hrr.pow 2)).add
      (((contDiffAt_const.mul hb).mul hrr).mul htr)).add (hc.mul (htr.pow 2)),
    (((ha.mul hrr).mul hrt).add
      (hb.mul ((hrr.mul htt).add (htr.mul hrt)))).add ((hc.mul htr).mul htt),
    ((ha.mul (hrt.pow 2)).add
      (((contDiffAt_const.mul hb).mul hrt).mul htt)).add (hc.mul (htt.pow 2))⟩

theorem n07a_localPullback_principal_smooth {U : Set PolarPoint} (hU : IsOpen U)
    {L : SymmetricCoefficients} {F : PolarPoint → PolarPoint}
    (ha : ContDiffOn ℝ ∞ L.a U) (hb : ContDiffOn ℝ ∞ L.b U)
    (hc : ContDiffOn ℝ ∞ L.c U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (n07aPullbackPrincipal L F).a U ∧
      ContDiffOn ℝ ∞ (n07aPullbackPrincipal L F).b U ∧
      ContDiffOn ℝ ∞ (n07aPullbackPrincipal L F).c U := by
  have hrr := n07a_localPullback_radial_smooth hU hF.fst
  have htr := n07a_localPullback_angular_smooth hU hF.fst
  have hrt := n07a_localPullback_radial_smooth hU hF.snd
  have htt := n07a_localPullback_angular_smooth hU hF.snd
  exact ⟨((ha.mul (hrr.pow 2)).add
      (((contDiffOn_const.mul hb).mul hrr).mul htr)).add (hc.mul (htr.pow 2)),
    (((ha.mul hrr).mul hrt).add
      (hb.mul ((hrr.mul htt).add (htr.mul hrt)))).add ((hc.mul htr).mul htt),
    ((ha.mul (hrt.pow 2)).add
      (((contDiffOn_const.mul hb).mul hrt).mul htt)).add (hc.mul (htt.pow 2))⟩

theorem n07a_localPullback_normalCoefficients_smooth
    {U V : Set PolarPoint} (hU : IsOpen U)
    {L : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    (ha : ContDiffOn ℝ ∞ L.a U) (hb : ContDiffOn ℝ ∞ L.b U)
    (hc : ContDiffOn ℝ ∞ L.c U) (hF : ContDiffOn ℝ ∞ F U)
    (hG : ContDiffOn ℝ ∞ G V) (hmap : MapsTo G V U)
    (hne : ∀ y ∈ V, (n07aPullbackPrincipal L F).a (G y) ≠ 0) :
    ∀ i, ContDiffOn ℝ ∞ (n07aPullbackNormalCoefficients L F G i) V := by
  have hp := n07a_localPullback_principal_smooth hU ha hb hc hF
  have hα := hp.1.comp hG hmap
  have hβ := hp.2.1.comp hG hmap
  have hγ := hp.2.2.comp hG hmap
  have hδ := (n07b_contDiffOn_divergenceOperator hU ha hb hc hF.fst).comp hG hmap
  have hη := (n07b_contDiffOn_divergenceOperator hU ha hb hc hF.snd).comp hG hmap
  intro i
  fin_cases i
  · exact (contDiffOn_const.mul hβ).div hα hne
  · exact hγ.neg.div hα hne
  · exact hδ.neg.div hα hne
  · exact hη.neg.div hα hne
  · exact contDiffOn_const
  · exact hα.inv hne

theorem n07a_localPullback_radial_chain
    {F : PolarPoint → PolarPoint} {v : PolarPoint → ℝ} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hv : DifferentiableAt ℝ v (F x)) :
    radialPartial (v ∘ F) x =
      radialPartial (fun q => (F q).1) x * radialPartial v (F x) +
        radialPartial (fun q => (F q).2) x * angularPartial v (F x) := by
  have hR : (fderiv ℝ F x (1, 0)).1 = radialPartial (fun q => (F q).1) x := by
    rw [radialPartial, fderiv.fst hF, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst']
  have hT : (fderiv ℝ F x (1, 0)).2 = radialPartial (fun q => (F q).2) x := by
    rw [radialPartial, fderiv.snd hF, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd']
  have he : fderiv ℝ F x (1, 0) =
      (fderiv ℝ F x (1, 0)).1 • (1, 0) +
        (fderiv ℝ F x (1, 0)).2 • (0, 1) := by
    ext <;> simp
  calc
    _ = fderiv ℝ v (F x) (fderiv ℝ F x (1, 0)) := by
      rw [radialPartial, fderiv_comp _ hv hF, ContinuousLinearMap.comp_apply]
    _ = (fderiv ℝ F x (1, 0)).1 * radialPartial v (F x) +
        (fderiv ℝ F x (1, 0)).2 * angularPartial v (F x) := by
      conv_lhs => rw [he]
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul, radialPartial, angularPartial]
    _ = _ := by rw [hR, hT]

theorem n07a_localPullback_angular_chain
    {F : PolarPoint → PolarPoint} {v : PolarPoint → ℝ} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hv : DifferentiableAt ℝ v (F x)) :
    angularPartial (v ∘ F) x =
      angularPartial (fun q => (F q).1) x * radialPartial v (F x) +
        angularPartial (fun q => (F q).2) x * angularPartial v (F x) := by
  have hR : (fderiv ℝ F x (0, 1)).1 = angularPartial (fun q => (F q).1) x := by
    rw [angularPartial, fderiv.fst hF, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst']
  have hT : (fderiv ℝ F x (0, 1)).2 = angularPartial (fun q => (F q).2) x := by
    rw [angularPartial, fderiv.snd hF, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd']
  have he : fderiv ℝ F x (0, 1) =
      (fderiv ℝ F x (0, 1)).1 • (1, 0) +
        (fderiv ℝ F x (0, 1)).2 • (0, 1) := by
    ext <;> simp
  calc
    _ = fderiv ℝ v (F x) (fderiv ℝ F x (0, 1)) := by
      rw [angularPartial, fderiv_comp _ hv hF, ContinuousLinearMap.comp_apply]
    _ = (fderiv ℝ F x (0, 1)).1 * radialPartial v (F x) +
        (fderiv ℝ F x (0, 1)).2 * angularPartial v (F x) := by
      conv_lhs => rw [he]
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul, radialPartial, angularPartial]
    _ = _ := by rw [hR, hT]

/-- The two drift coefficients are the actual operator applied to the coordinates. -/
theorem n07a_localPullback_divergence_chain
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {L : SymmetricCoefficients} {F : PolarPoint → PolarPoint} {v : PolarPoint → ℝ}
    (ha : ContDiffOn ℝ ∞ L.a U) (hb : ContDiffOn ℝ ∞ L.b U)
    (hc : ContDiffOn ℝ ∞ L.c U) (hF : ContDiffOn ℝ ∞ F U)
    (hv : ContDiffOn ℝ ∞ v V) (hmap : MapsTo F U V) :
    EqOn (divergenceOperator L (v ∘ F))
      (fun x => (n07aPullbackPrincipal L F).a x * mixedDerivative 2 0 v (F x) +
        2 * (n07aPullbackPrincipal L F).b x * mixedDerivative 1 1 v (F x) +
        (n07aPullbackPrincipal L F).c x * mixedDerivative 0 2 v (F x) +
        divergenceOperator L (fun q => (F q).1) x * mixedDerivative 1 0 v (F x) +
        divergenceOperator L (fun q => (F q).2) x * mixedDerivative 0 1 v (F x)) U := by
  let R := fun q => (F q).1
  let T := fun q => (F q).2
  let Nr := fun q => L.a q * radialPartial R q + L.b q * angularPartial R q
  let Nt := fun q => L.a q * radialPartial T q + L.b q * angularPartial T q
  let Ar := fun q => L.b q * radialPartial R q + L.c q * angularPartial R q
  let At := fun q => L.b q * radialPartial T q + L.c q * angularPartial T q
  have hRr := n07a_localPullback_radial_smooth hU hF.fst
  have hRt := n07a_localPullback_angular_smooth hU hF.fst
  have hTr := n07a_localPullback_radial_smooth hU hF.snd
  have hTt := n07a_localPullback_angular_smooth hU hF.snd
  have hNr : ContDiffOn ℝ ∞ Nr U := (ha.mul hRr).add (hb.mul hRt)
  have hNt : ContDiffOn ℝ ∞ Nt U := (ha.mul hTr).add (hb.mul hTt)
  have hAr : ContDiffOn ℝ ∞ Ar U := (hb.mul hRr).add (hc.mul hRt)
  have hAt : ContDiffOn ℝ ∞ At U := (hb.mul hTr).add (hc.mul hTt)
  have hvr := n07a_localPullback_radial_smooth hV hv
  have hvt := n07a_localPullback_angular_smooth hV hv
  have hvrF := hvr.comp hF hmap
  have hvtF := hvt.comp hF hmap
  intro x hx
  have hdF := (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdvr := (hvr.contDiffAt (hV.mem_nhds (hmap hx))).differentiableAt (by simp)
  have hdvt := (hvt.contDiffAt (hV.mem_nhds (hmap hx))).differentiableAt (by simp)
  have hdNr := (hNr.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdNt := (hNt.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdAr := (hAr.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdAt := (hAt.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdvrF := (hvrF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdvtF := (hvtF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hnormal :
      (fun q => L.a q * radialPartial (v ∘ F) q + L.b q * angularPartial (v ∘ F) q)
        =ᶠ[𝓝 x] (fun q => Nr q * (radialPartial v ∘ F) q +
          Nt q * (angularPartial v ∘ F) q) := by
    filter_upwards [hU.mem_nhds hx] with q hq
    have hqF := (hF.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
    have hqv := (hv.contDiffAt (hV.mem_nhds (hmap hq))).differentiableAt (by simp)
    rw [n07a_localPullback_radial_chain hqF hqv, n07a_localPullback_angular_chain hqF hqv]
    dsimp only [Nr, Nt, R, T, Function.comp_apply]
    ring
  have hangular :
      (fun q => L.b q * radialPartial (v ∘ F) q + L.c q * angularPartial (v ∘ F) q)
        =ᶠ[𝓝 x] (fun q => Ar q * (radialPartial v ∘ F) q +
          At q * (angularPartial v ∘ F) q) := by
    filter_upwards [hU.mem_nhds hx] with q hq
    have hqF := (hF.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
    have hqv := (hv.contDiffAt (hV.mem_nhds (hmap hq))).differentiableAt (by simp)
    rw [n07a_localPullback_radial_chain hqF hqv, n07a_localPullback_angular_chain hqF hqv]
    dsimp only [Ar, At, R, T, Function.comp_apply]
    ring
  have hnormal' := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) hnormal.fderiv_eq
  have hangular' := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) hangular.fderiv_eq
  have hrr : radialPartial (radialPartial v) (F x) = mixedDerivative 2 0 v (F x) :=
    (radialPartial_eq_mixedDerivative_on hV hvr (hmap hx)).trans
      (mixedDerivative_radialPartial hV hv 1 0 (hmap hx))
  have hrt : angularPartial (radialPartial v) (F x) = mixedDerivative 1 1 v (F x) :=
    (angularPartial_eq_mixedDerivative_on hV hvr (hmap hx)).trans
      (mixedDerivative_radialPartial hV hv 0 1 (hmap hx))
  have htt : angularPartial (angularPartial v) (F x) = mixedDerivative 0 2 v (F x) :=
    (angularPartial_eq_mixedDerivative_on hV hvt (hmap hx)).trans
      (mixedDerivative_angularPartial hV hv 0 1 (hmap hx))
  change radialPartial _ x + angularPartial _ x = _
  rw [show radialPartial _ x = radialPartial
      (fun q => Nr q * (radialPartial v ∘ F) q + Nt q * (angularPartial v ∘ F) q) x
      from hnormal',
    show angularPartial _ x = angularPartial
      (fun q => Ar q * (radialPartial v ∘ F) q + At q * (angularPartial v ∘ F) q) x
      from hangular',
    radialPartial_add (hdNr.fun_mul hdvrF) (hdNt.fun_mul hdvtF),
    angularPartial_add (hdAr.fun_mul hdvrF) (hdAt.fun_mul hdvtF),
    radialPartial_mul hdNr hdvrF, radialPartial_mul hdNt hdvtF,
    angularPartial_mul hdAr hdvrF, angularPartial_mul hdAt hdvtF,
    n07a_localPullback_radial_chain hdF hdvr, n07a_localPullback_radial_chain hdF hdvt,
    n07a_localPullback_angular_chain hdF hdvr, n07a_localPullback_angular_chain hdF hdvt,
    radial_angular_commute ((hv.contDiffAt (hV.mem_nhds (hmap hx))).of_le (by simp)),
    hrr, hrt, htt,
    radialPartial_eq_mixedDerivative_on hV hv (hmap hx),
    angularPartial_eq_mixedDerivative_on hV hv (hmap hx)]
  dsimp only [Function.comp_apply, n07aPullbackPrincipal, divergenceOperator, Nr, Nt, Ar, At, R, T]
  ring

private theorem n07a_localPullback_normal_algebra
    {a b c d e r rr rt tt ur ut f : ℝ} (ha : a ≠ 0)
    (heq : a * rr + 2 * b * rt + c * tt + d * ur + e * ut = f) :
    rr = (-2 * b / a) * rt + (-c / a) * tt + (-d / a) * ur +
      (-e / a) * ut + 0 * r + a⁻¹ * f := by
  apply (mul_left_cancel₀ ha)
  field_simp [ha]
  nlinarith only [heq]

/-- A genuine physical equation gives the normalized equation for the
ungauged pullback. The sets can be either open side of a local cut. -/
theorem n07a_localPullback_normal_equation
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {L : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    (ha : ContDiffOn ℝ ∞ L.a U) (hb : ContDiffOn ℝ ∞ L.b U)
    (hc : ContDiffOn ℝ ∞ L.c U) (hF : ContDiffOn ℝ ∞ F U)
    (hG : ContDiffOn ℝ ∞ G V) (hFmap : MapsTo F U V) (hGmap : MapsTo G V U)
    (hGF : ∀ x ∈ U, G (F x) = x) (hFG : ∀ y ∈ V, F (G y) = y)
    {u f : PolarPoint → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (heq : EqOn (divergenceOperator L u) f U)
    (hne : ∀ y ∈ V, (n07aPullbackPrincipal L F).a (G y) ≠ 0) :
    EqOn (mixedDerivative 2 0 (u ∘ G))
      (n07aNormalRhs (n07aPullbackNormalCoefficients L F G) (u ∘ G) (f ∘ G)) V := by
  let v := u ∘ G
  have hv : ContDiffOn ℝ ∞ v V := hu.comp hG hGmap
  have hrep : EqOn (v ∘ F) u U := fun x hx => congrArg u (hGF x hx)
  intro y hy
  have hnear : (v ∘ F) =ᶠ[𝓝 (G y)] u := by
    filter_upwards [hU.mem_nhds (hGmap hy)] with x hx
    exact hrep hx
  have hd : fderiv ℝ (v ∘ F) =ᶠ[𝓝 (G y)] fderiv ℝ u := hnear.fderiv
  have hNr :
      (fun x => L.a x * radialPartial (v ∘ F) x + L.b x * angularPartial (v ∘ F) x)
        =ᶠ[𝓝 (G y)] (fun x => L.a x * radialPartial u x + L.b x * angularPartial u x) := by
    filter_upwards [hd] with x hx
    simp only [radialPartial, angularPartial, hx]
  have hAt :
      (fun x => L.b x * radialPartial (v ∘ F) x + L.c x * angularPartial (v ∘ F) x)
        =ᶠ[𝓝 (G y)] (fun x => L.b x * radialPartial u x + L.c x * angularPartial u x) := by
    filter_upwards [hd] with x hx
    simp only [radialPartial, angularPartial, hx]
  have hdiv : divergenceOperator L (v ∘ F) (G y) = divergenceOperator L u (G y) :=
    congrArg₂ (fun r t : PolarPoint →L[ℝ] ℝ => r (1, 0) + t (0, 1))
      hNr.fderiv_eq hAt.fderiv_eq
  have hchain := n07a_localPullback_divergence_chain hU hV ha hb hc hF hv hFmap (hGmap hy)
  dsimp only at hchain
  rw [hFG y hy] at hchain
  have hsource := hchain.symm.trans (hdiv.trans (heq (hGmap hy)))
  have hn := n07a_localPullback_normal_algebra (r := v y) (hne y hy) hsource
  simpa [n07aNormalRhs, n07aPullbackNormalCoefficients, n07aNormalShift,
    Fin.sum_univ_succ, spaces_mixedDerivative_zero, Function.comp_apply, v] using hn

end ContinuousFlexibility.Analysis
