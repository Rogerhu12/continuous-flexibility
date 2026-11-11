import ContinuousFlexibility.Analysis.N01cFlowAffineCompression
import ContinuousFlexibility.Analysis.N01cAngularJetTowers
import ContinuousFlexibility.Analysis.N01cCircleLinearVariationSmooth
import ContinuousFlexibility.Analysis.OneHighCircleFourierCompositionCalculus

/-!
# The actual higher flow variations satisfy the circle Sobolev estimate

The ordinary classical flow first supplies genuine joint smoothness in
finite parameters, time and initial angle. Its positive parameter jets
are periodic functions of the initial angle. Their exact time equation
has the actual first angular speed derivative as its linear coefficient
and the already constructed strictly lower-order forcing as its source.
This builds the inputs of the circle linear estimate from the actual
flow; no parameter derivative or norm bound of the flow is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

section GlobalRegularity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Initial-angle translation converts the initial condition to zero,
so the established parameter theorem supplies all joint derivatives. -/
theorem contDiff_globalCircleVectorFlow
    {G Θ : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q α, Θ (q, (0, α)) = α)
    (hflow : ∀ q t α, HasDerivAt (fun r => Θ (q, (r, α)))
      (G (q, (t, Θ (q, (t, α))))) t) : ContDiff ℝ ∞ Θ := by
  let H : (E × ℝ) × PolarPoint → ℝ := fun p =>
    G (p.1.1, (p.2.1, p.2.2 + p.1.2))
  let Φ : (E × ℝ) × ℝ → ℝ := fun p => Θ (p.1.1, (p.2, p.1.2)) - p.1.2
  have hH : ContDiff ℝ ∞ H :=
    hG.comp (contDiff_fst.fst.prodMk
      (contDiff_snd.fst.prodMk (contDiff_snd.snd.add contDiff_fst.snd)))
  have hΦ : Continuous Φ :=
    (hΘ.comp (continuous_fst.fst.prodMk
      (continuous_snd.prodMk continuous_fst.snd))).sub continuous_fst.snd
  have hΦinit (q : E × ℝ) : Φ (q, 0) = 0 := by
    change Θ (q.1, (0, q.2)) - q.2 = 0
    rw [hinit, sub_self]
  have hΦflow (q : E × ℝ) (t : ℝ) :
      HasDerivAt (fun r => Φ (q, r)) (H (q, (t, Φ (q, t)))) t := by
    simpa only [Φ, H, sub_add_cancel] using (hflow q.1 t q.2).sub_const q.2
  have hs := contDiff_globalCircleVectorTrajectory hH hΦ hΦinit hΦflow
  have hback : ContDiff ℝ ∞
      (fun p : E × PolarPoint => Φ ((p.1, p.2.2), p.2.1) + p.2.2) :=
    (hs.comp ((contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst)).add
      contDiff_snd.snd
  simpa only [Φ, sub_add_cancel] using hback

end GlobalRegularity

section ParameterFields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def flowParameterField (F : E × PolarPoint → ℝ) (n : ℕ)
    (q : E) (v : Fin n → E) (p : PolarPoint) : ℝ :=
  iteratedFDeriv ℝ n (fun x => F (x, p)) q v

theorem flowParameterField_eq_joint {F : E × PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (q : E) (v : Fin n → E) (p : PolarPoint) :
    flowParameterField F n q v p =
      iteratedFDeriv ℝ n F (q, p) (fun i => (v i, (0 : PolarPoint))) := by
  let J : SmoothDirections (univ : Set (E × PolarPoint)) F :=
    smoothDirectionsOfJets isOpen_univ (fun k => iteratedFDeriv ℝ k F)
      (hasProjectiveJetsOn_of_contDiffOn isOpen_univ hF.contDiffOn)
  have h := smoothDirections_iteratedFDeriv_finiteAffine J (0, p)
    (ContinuousLinearMap.inl ℝ E PolarPoint) n (y := q) (mem_univ _) v
  dsimp only [J, smoothDirectionsOfJets] at h
  simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk,
    zero_add, add_zero, flowParameterField] using h

theorem contDiff_flowParameterField {F : E × PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (q : E) (v : Fin n → E) :
    ContDiff ℝ ∞ (flowParameterField F n q v) := by
  have he : flowParameterField F n q v =
      fun p => iteratedFDeriv ℝ n F (q, p) (fun i => (v i, (0 : PolarPoint))) :=
    funext (flowParameterField_eq_joint hF n q v)
  rw [he]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E × PolarPoint) ℝ
    (fun i => (v i, (0 : PolarPoint)))).contDiff.comp
      ((hF.iteratedFDeriv_right (m := ∞) (i := n) (by simp)).comp
        (contDiff_const.prodMk contDiff_id))

theorem flowParameterField_periodic {F : E × PolarPoint → ℝ} {P : ℝ}
    (hp : ∀ q t, Function.Periodic (fun α => F (q, (t, α))) P)
    (n : ℕ) (q : E) (v : Fin n → E) (t : ℝ) :
    Function.Periodic (fun α => flowParameterField F n q v (t, α)) P := by
  intro α
  have he : (fun x => F (x, (t, α + P))) = fun x => F (x, (t, α)) :=
    funext (fun x => hp x t α)
  simp only [flowParameterField, he]

theorem flowParameterField_periodic_of_lift {F : E × PolarPoint → ℝ} {P : ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hp : ∀ q t α, F (q, (t, α + P)) = F (q, (t, α)) + P)
    (n : ℕ) (q : E) (v : Fin (n + 1) → E) (t : ℝ) :
    Function.Periodic (fun α => flowParameterField F (n + 1) q v (t, α)) P := by
  intro α
  have he : (fun x => F (x, (t, α + P))) = fun x => F (x, (t, α)) + P :=
    funext (fun x => hp x t α)
  have hf : ContDiffAt ℝ (n + 1) (fun x => F (x, (t, α))) q :=
    (hF.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
  simp only [flowParameterField, he,
    fun_iteratedFDeriv_add_apply hf contDiffAt_const,
    ContinuousMultilinearMap.add_apply, iteratedFDeriv_succ_const,
    Pi.zero_apply, ContinuousMultilinearMap.zero_apply, add_zero]

def flowInitialSlice (Θ : E × PolarPoint → ℝ) (α : ℝ) (p : E × ℝ) : ℝ :=
  Θ (p.1, (p.2, α))

theorem contDiff_flowInitialSlice {Θ : E × PolarPoint → ℝ}
    (hΘ : ContDiff ℝ ∞ Θ) (α : ℝ) : ContDiff ℝ ∞ (flowInitialSlice Θ α) :=
  hΘ.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

def flowVariationCoefficient (G Θ : E × PolarPoint → ℝ) (q : E) (p : PolarPoint) : ℝ :=
  fderiv ℝ G (q, (p.1, Θ (q, p))) (0, (0, 1))

theorem speedAlongFlowAngularJet_eq_coefficient
    {G Θ : E × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (J : ContinuousTimeSpeedTower (univ : Set E) G) (q : E) (p : PolarPoint) :
    speedAlongFlowAngularJet J (flowInitialSlice Θ p.2) (q, p.1) =
      flowVariationCoefficient G Θ q p := by
  have hj := (J.jet p.1).hasDerivAt_angle (mem_univ q) (Θ (q, p))
  have hg : HasDerivAt (fun α => G (q, (p.1, α)))
      (flowVariationCoefficient G Θ q p) (Θ (q, p)) := by
    exact (hG.differentiable (by simp) (q, (p.1, Θ (q, p)))).hasFDerivAt.comp_hasDerivAt
      (Θ (q, p)) ((hasDerivAt_const _ q).prodMk
        ((hasDerivAt_const _ p.1).prodMk (hasDerivAt_id' _)))
  have he : (Fin.cons ((0 : E), (1 : ℝ)) Fin.elim0 : Fin 1 → E × ℝ) =
      fun _ => (0, 1) := by
    funext i
    fin_cases i
    rfl
  simpa only [projectiveFirstJetValue, he, speedAlongFlowAngularJet,
    flowTrajectoryGraph, flowInitialSlice, ContinuousTimeSpeedTower.D] using hj.unique hg

theorem flowVariationCoefficient_eq_deriv
    {G Θ : E × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G) (q : E) (p : PolarPoint) :
    flowVariationCoefficient G Θ q p =
      deriv (fun α => G (q, (p.1, α))) (Θ (q, p)) := by
  have hd : HasDerivAt (fun α => G (q, (p.1, α)))
      (flowVariationCoefficient G Θ q p) (Θ (q, p)) :=
    (hG.differentiable (by simp) (q, (p.1, Θ (q, p)))).hasFDerivAt.comp_hasDerivAt
      (Θ (q, p)) ((hasDerivAt_const _ q).prodMk
        ((hasDerivAt_const _ p.1).prodMk (hasDerivAt_id' _)))
  exact hd.deriv.symm

theorem contDiff_flowVariationCoefficient {G Θ : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ ∞ Θ) (q : E) :
    ContDiff ℝ ∞ (flowVariationCoefficient G Θ q) :=
  ((hG.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_const.prodMk (contDiff_fst.prodMk
      (hΘ.comp (contDiff_const.prodMk contDiff_id))))).clm_apply contDiff_const

theorem flowVariationCoefficient_periodic {G Θ : E × PolarPoint → ℝ} {P : ℝ}
    [Fact (0 < P)] (hG : ContDiff ℝ ∞ G)
    (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
    (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)
    (q : E) (t : ℝ) :
    Function.Periodic (fun α => flowVariationCoefficient G Θ q (t, α)) P := by
  intro α
  change flowVariationCoefficient G Θ q (t, α + P) =
    flowVariationCoefficient G Θ q (t, α)
  rw [flowVariationCoefficient_eq_deriv hG q (t, α + P),
    flowVariationCoefficient_eq_deriv hG q (t, α), hΘp q t α]
  exact periodic_circle_deriv (hGp q t) (Θ (q, (t, α)))

/-- This is exactly the previously defined truncated lower forcing,
evaluated on the actual parameter jets of the supplied flow. -/
def flowVariationForcing {G Θ : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower (univ : Set E) G) (hΘ : ContDiff ℝ ∞ Θ)
    (N : ℕ) (q : E) (v : Fin N → E) (p : PolarPoint) : ℝ :=
  truncatedFlowForcing J (flowInitialSlice Θ p.2)
    (fun k (_ : k < N) => canonicalFlowVariation (contDiff_flowInitialSlice hΘ p.2) k)
    (q, p.1) v

theorem flowVariationForcing_eq_source_sub
    {G Θ : E × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (J : ContinuousTimeSpeedTower (univ : Set E) G) (hΘ : ContDiff ℝ ∞ Θ)
    {N : ℕ} (hN : 0 < N) (q : E) (v : Fin N → E) (p : PolarPoint) :
    flowVariationForcing J hΘ N q v p =
      flowParameterField (fun z => G (z.1, (z.2.1, Θ z))) N q v p -
        flowVariationCoefficient G Θ q p * flowParameterField Θ N q v p := by
  have h := (iteratedFDeriv_speed_along_flow_eq_partitionSum J
    (contDiff_flowInitialSlice hΘ p.2) N q p.1 v).trans
      (flowJetComposition_eq_linear_add_truncated J (flowInitialSlice Θ p.2)
        (canonicalFlowVariation (contDiff_flowInitialSlice hΘ p.2)) hN (q, p.1) v)
  rw [speedAlongFlowAngularJet_eq_coefficient (Θ := Θ) hG J q p] at h
  change flowParameterField (fun z => G (z.1, (z.2.1, Θ z))) N q v p =
    flowVariationCoefficient G Θ q p * flowParameterField Θ N q v p +
      flowVariationForcing J hΘ N q v p at h
  linarith

theorem contDiff_flowVariationForcing
    {G Θ : E × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (J : ContinuousTimeSpeedTower (univ : Set E) G) (hΘ : ContDiff ℝ ∞ Θ)
    {N : ℕ} (hN : 0 < N) (q : E) (v : Fin N → E) :
    ContDiff ℝ ∞ (flowVariationForcing J hΘ N q v) := by
  have he : flowVariationForcing J hΘ N q v = fun p =>
      flowParameterField (fun z => G (z.1, (z.2.1, Θ z))) N q v p -
        flowVariationCoefficient G Θ q p * flowParameterField Θ N q v p :=
    funext (flowVariationForcing_eq_source_sub hG J hΘ hN q v)
  rw [he]
  exact (contDiff_flowParameterField
    (hG.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk hΘ))) N q v).sub
      ((contDiff_flowVariationCoefficient hG hΘ q).mul (contDiff_flowParameterField hΘ N q v))

theorem flowVariationForcing_periodic
    {G Θ : E × PolarPoint → ℝ} {P : ℝ} [Fact (0 < P)]
    (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hΘ : ContDiff ℝ ∞ Θ)
    (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
    (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)
    (n : ℕ) (q : E) (v : Fin (n + 1) → E) (t : ℝ) :
    Function.Periodic (fun α => flowVariationForcing J hΘ (n + 1) q v (t, α)) P := by
  have hsource : ∀ x r, Function.Periodic (fun α => G (x, (r, Θ (x, (r, α))))) P := by
    intro x r α
    change G (x, (r, Θ (x, (r, α + P)))) = G (x, (r, Θ (x, (r, α))))
    rw [hΘp x r α]
    exact hGp x r _
  intro α
  change flowVariationForcing J hΘ (n + 1) q v (t, α + P) =
    flowVariationForcing J hΘ (n + 1) q v (t, α)
  rw [flowVariationForcing_eq_source_sub hG J hΘ (Nat.succ_pos n) q v (t, α + P),
    flowVariationForcing_eq_source_sub hG J hΘ (Nat.succ_pos n) q v (t, α)]
  exact congrArg₂ (fun a b : ℝ => a - b)
    (flowParameterField_periodic (F := fun z => G (z.1, (z.2.1, Θ z)))
      hsource (n + 1) q v t α)
    (congrArg₂ (fun a b : ℝ => a * b)
      (flowVariationCoefficient_periodic hG hGp hΘp q t α)
      (flowParameterField_periodic_of_lift hΘ hΘp n q v t α))

end ParameterFields

section CircleData

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {G Θ : E × PolarPoint → ℝ} {P : ℝ} [Fact (0 < P)]
  (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
  (hΘ : Continuous Θ) (hinit : ∀ q α, Θ (q, (0, α)) = α)
  (hflow : ∀ q t α, HasDerivAt (fun r => Θ (q, (r, α)))
    (G (q, (t, Θ (q, (t, α))))) t)
  (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
  (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)

/-- The positive parameter variation of the supplied classical flow,
with its actual coefficient and strictly lower-order forcing. -/
def flowParameterCircleVariationData (b : ℝ) (n : ℕ) (q : E)
    (v : Fin (n + 1) → E) : CircleLinearVariationData P 0 b := by
  let hs : ContDiff ℝ ∞ Θ := contDiff_globalCircleVectorFlow hG hΘ hinit hflow
  refine circleLinearVariationOfSmooth
    (contDiff_flowParameterField hs (n + 1) q v)
    (contDiff_flowVariationCoefficient hG hs q)
    (contDiff_flowVariationForcing hG J hs (Nat.succ_pos n) q v)
    (flowParameterField_periodic_of_lift hs hΘp n q v)
    (flowVariationCoefficient_periodic hG hGp hΘp q)
    (flowVariationForcing_periodic hG J hs hGp hΘp n q v) ?_ ?_
  · intro α
    exact globalCircleVectorTrajectory_parameterJet_initial
      (Θ := flowInitialSlice Θ α) (fun x => hinit x α) n q v
  · intro t _ α
    have hd := globalCircleVectorTrajectory_parameterJet_linearODE
      J hG (contDiff_flowInitialSlice hs α).continuous
      (fun x => hinit x α) (fun x r => hflow x r α)
      (Nat.succ_pos n) q t v
    change HasDerivAt
      (fun r => flowParameterField Θ (n + 1) q v (r, α))
      (speedAlongFlowAngularJet J (flowInitialSlice Θ α) (q, t) *
        flowParameterField Θ (n + 1) q v (t, α) +
        flowVariationForcing J hs (n + 1) q v (t, α)) t at hd
    simpa only [speedAlongFlowAngularJet_eq_coefficient (Θ := Θ) hG J q (t, α)] using hd

/-- The circle value is the actual angular derivative of the actual
positive parameter derivative, not an independently assigned jet. -/
theorem flowParameterCircleVariationData_value (b : ℝ) (n : ℕ) (q : E)
    (v : Fin (n + 1) → E) (t : ℝ) (j : ℕ) (α : ℝ) :
    (flowParameterCircleVariationData hG J hΘ hinit hflow hGp hΘp b n q v).value
        t j (α : AddCircle P) =
      iteratedDeriv j (fun η => flowParameterField Θ (n + 1) q v (t, η)) α := by
  let hs : ContDiff ℝ ∞ Θ := contDiff_globalCircleVectorFlow hG hΘ hinit hflow
  change circleFlowSpeedJet (flowParameterField Θ (n + 1) q v)
    (contDiff_flowParameterField hs (n + 1) q v)
    (flowParameterField_periodic_of_lift hs hΘp n q v) t j
    (α : AddCircle P) = _
  exact circleFlowSpeedJet_coe_apply (flowParameterField Θ (n + 1) q v)
    (contDiff_flowParameterField hs (n + 1) q v)
    (flowParameterField_periodic_of_lift hs hΘp n q v) t j α

/-- The actual higher variation has one high forcing or coefficient
factor, with its exponential constant depending only on the low
coefficient integral. -/
theorem flowParameterCircleVariationData_sobolev_le (b : ℝ) (n : ℕ) (q : E)
    (v : Fin (n + 1) → E) (s : ℕ) {t : ℝ} (ht : t ∈ Icc 0 b) :
    let V := flowParameterCircleVariationData hG J hΘ hinit hflow hGp hΘp b n q v
    V.valueNorm s t ≤ circleLinearVariationSobolevConstant P (V.coefficientSize 1) s *
      (V.forcingSize s + V.coefficientSize s * V.forcingSize 1) :=
  (flowParameterCircleVariationData hG J hΘ hinit hflow hGp hΘp b n q v).sobolev_le s ht

end CircleData

end ContinuousFlexibility.Analysis
