module

public import ContinuousFlexibility.Analysis.N01cFlowVariationCircleData
public import ContinuousFlexibility.Analysis.N01cFlowForcingSobolev

/-!
# The actual variational forcing has a one-high circle estimate

Every factor in the ordered-partition forcing is now proved smooth and
periodic from the actual smooth speed and actual smooth flow. Thus the
finite product estimate applies without an additional regularity
hypothesis on the forcing factors. Its right side retains the actual
selected speed jets and strict lower parameter variations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff ENNReal BigOperators

section ForcingAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

section SpeedFields

variable {G : E × PolarPoint → ℝ}
  (J : ContinuousTimeSpeedTower (univ : Set E) G)

/-- A mixed state-and-angle speed jet, with time left as a variable. -/
def flowSpeedJointField (n : ℕ) (q : E) (v : Fin n → E × ℝ)
    (p : PolarPoint) : ℝ :=
  J.D n (q, p) v

theorem flowSpeedJointField_eq_joint (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (q : E) (v : Fin n → E × ℝ) (p : PolarPoint) :
    flowSpeedJointField J n q v p =
      iteratedFDeriv ℝ n G (q, p)
        (fun i => speedTimeSliceInjection (v i)) := by
  have he := (J.jet p.1).hasProjectiveJetsOn.eq_iteratedFDeriv_finiteDimensional
    (J.jet p.1).open_domain n (x := (q, p.2)) ⟨mem_univ _, mem_univ _⟩
  have heval := congrArg (fun A : (E × ℝ) [×n]→L[ℝ] ℝ => A v) he
  change flowSpeedJointField J n q v p =
    iteratedFDeriv ℝ n (fun y : E × ℝ => G (y.1, (p.1, y.2))) (q, p.2) v at heval
  exact heval.trans (iteratedFDeriv_speed_timeSlice hG n p.1 (q, p.2) v)

theorem contDiff_flowSpeedJointField (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (q : E) (v : Fin n → E × ℝ) :
    ContDiff ℝ ∞ (flowSpeedJointField J n q v) := by
  have he : flowSpeedJointField J n q v =
      fun p => iteratedFDeriv ℝ n G (q, p)
        (fun i => speedTimeSliceInjection (v i)) :=
    funext (flowSpeedJointField_eq_joint J hG n q v)
  rw [he]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E × PolarPoint) ℝ
    (fun i => speedTimeSliceInjection (v i))).contDiff.comp
      ((hG.iteratedFDeriv_right (m := ∞) (i := n) (by simp)).comp
        (contDiff_const.prodMk contDiff_id))

/-- Periodicity differentiates through all state-and-angle slots. The
translation is affine, so its actual higher derivatives are unchanged. -/
theorem flowSpeedJointField_periodic {P : ℝ}
    (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
    (n : ℕ) (q : E) (v : Fin n → E × ℝ) (t : ℝ) :
    Function.Periodic (fun α => flowSpeedJointField J n q v (t, α)) P := by
  intro α
  have hpoint : ((0 : E), P) +
      (ContinuousLinearMap.id ℝ (E × ℝ)) (q, α) ∈
        (univ : Set E) ×ˢ (univ : Set ℝ) := ⟨mem_univ _, mem_univ _⟩
  have ha := smoothDirections_iteratedFDeriv_finiteAffine (J.jet t)
    ((0 : E), P) (ContinuousLinearMap.id ℝ (E × ℝ)) n hpoint v
  have hshift :
      iteratedFDeriv ℝ n (fun y : E × ℝ => G (y.1, (t, P + y.2))) (q, α) v =
        (J.jet t).D n (q, P + α) v := by
    simpa only [ContinuousLinearMap.id_apply, Prod.fst_add, Prod.snd_add,
      Prod.mk_add_mk, zero_add] using ha
  have he : (fun y : E × ℝ => G (y.1, (t, P + y.2))) =
      fun y => G (y.1, (t, y.2)) := by
    funext y
    rw [add_comm P y.2]
    exact hGp y.1 t y.2
  rw [he] at hshift
  have hbase := (J.jet t).hasProjectiveJetsOn.eq_iteratedFDeriv_finiteDimensional
    (J.jet t).open_domain n (x := (q, α)) ⟨mem_univ _, mem_univ _⟩
  change (J.jet t).D n (q, α + P) v = (J.jet t).D n (q, α) v
  rw [add_comm α P, ← hshift, hbase]

end SpeedFields

section CanonicalFactors

variable {G Θ : E × PolarPoint → ℝ}
  (J : ContinuousTimeSpeedTower (univ : Set E) G)
  (hΘ : ContDiff ℝ ∞ Θ)

include hΘ in
theorem flowParameterField_periodic_of_pos {P : ℝ}
    (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)
    {n : ℕ} (hn : 0 < n) (q : E) (v : Fin n → E) (t : ℝ) :
    Function.Periodic (fun α => flowParameterField Θ n q v (t, α)) P := by
  cases n with
  | zero => omega
  | succ n => exact flowParameterField_periodic_of_lift hΘ hΘp n q v t

include hΘ in
theorem contDiff_flowSelectedSpeedCoefficient
    (hG : ContDiff ℝ ∞ G) {N : ℕ}
    (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (q : E) (v : Fin N → E) (t : ℝ) :
    ContDiff ℝ ∞
      (fun α => flowSelectedSpeedCoefficient J (flowInitialSlice Θ α) c s (q, t) v) := by
  classical
  let w : Fin c.length → E × ℝ := fun i => if i ∈ s then
    ((flowParameterIdentityJet (c.partSize i) (v ∘ c.emb i)).1, 0) else (0, 1)
  have hangle : ContDiff ℝ ∞ (fun α : ℝ => Θ (q, (t, α))) :=
    hΘ.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  exact (contDiff_flowSpeedJointField J hG c.length q w).comp
    (contDiff_const.prodMk hangle)

theorem flowSelectedSpeedCoefficient_periodic {P : ℝ}
    (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
    (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)
    {N : ℕ} (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (q : E) (v : Fin N → E) (t : ℝ) :
    Function.Periodic
      (fun α => flowSelectedSpeedCoefficient J (flowInitialSlice Θ α) c s (q, t) v) P := by
  classical
  let w : Fin c.length → E × ℝ := fun i => if i ∈ s then
    ((flowParameterIdentityJet (c.partSize i) (v ∘ c.emb i)).1, 0) else (0, 1)
  intro α
  change flowSpeedJointField J c.length q w (t, Θ (q, (t, α + P))) =
    flowSpeedJointField J c.length q w (t, Θ (q, (t, α)))
  rw [hΘp]
  exact flowSpeedJointField_periodic J hGp c.length q w t _

theorem contDiff_flowSelectedLowerFactor {N : ℕ}
    (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (q : E) (v : Fin N → E) (t : ℝ) (i : Fin c.length) :
    ContDiff ℝ ∞ (fun α => flowSelectedLowerFactor
      (fun k (_ : k < N) => canonicalFlowVariation (contDiff_flowInitialSlice hΘ α) k)
      c s (q, t) v i) := by
  classical
  by_cases hi : i ∈ s
  · simpa only [flowSelectedLowerFactor, if_pos hi] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)))
  · by_cases hk : c.partSize i < N
    · simp only [flowSelectedLowerFactor, if_neg hi, lowerStateVariation, dif_pos hk]
      change ContDiff ℝ ∞ (fun α =>
        flowParameterField Θ (c.partSize i) q (v ∘ c.emb i) (t, α))
      exact (contDiff_flowParameterField hΘ (c.partSize i) q (v ∘ c.emb i)).comp
        (contDiff_const.prodMk contDiff_id)
    · simpa only [flowSelectedLowerFactor, if_neg hi, lowerStateVariation, dif_neg hk,
        zeroStateVariation, ContinuousMultilinearMap.zero_apply] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))

theorem flowSelectedLowerFactor_periodic {P : ℝ}
    (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)
    {N : ℕ} (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (q : E) (v : Fin N → E) (t : ℝ) (i : Fin c.length) :
    Function.Periodic (fun α => flowSelectedLowerFactor
      (fun k (_ : k < N) => canonicalFlowVariation (contDiff_flowInitialSlice hΘ α) k)
      c s (q, t) v i) P := by
  classical
  by_cases hi : i ∈ s
  · intro α
    simp only [flowSelectedLowerFactor, if_pos hi]
  · by_cases hk : c.partSize i < N
    · simp only [flowSelectedLowerFactor, if_neg hi, lowerStateVariation, dif_pos hk]
      exact flowParameterField_periodic_of_pos hΘ hΘp (c.partSize_pos i) q (v ∘ c.emb i) t
    · intro α
      simp only [flowSelectedLowerFactor, if_neg hi, lowerStateVariation, dif_neg hk,
        zeroStateVariation, ContinuousMultilinearMap.zero_apply]

/-- The factors use the actual finite-parameter derivatives of the same
flow, including the strict lower-order cutoff in the Volterra equation. -/
def canonicalFlowForcingFactors {N : ℕ} (q : E) (v : Fin N → E)
    (t : ℝ) (d : FlowForcingChoice N) : Fin (d.1.length + 1) → ℝ → ℝ :=
  flowForcingFactors J (flowInitialSlice Θ)
    (fun α k (_ : k < N) => canonicalFlowVariation (contDiff_flowInitialSlice hΘ α) k)
    (q, t) v d

theorem contDiff_canonicalFlowForcingFactors (hG : ContDiff ℝ ∞ G)
    {N : ℕ} (q : E) (v : Fin N → E) (t : ℝ)
    (d : FlowForcingChoice N) (i : Fin (d.1.length + 1)) :
    ContDiff ℝ ∞ (canonicalFlowForcingFactors J hΘ q v t d i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact contDiff_flowSelectedSpeedCoefficient J hΘ hG d.1 d.2 q v t
  · exact contDiff_flowSelectedLowerFactor hΘ d.1 d.2 q v t j

theorem canonicalFlowForcingFactors_periodic {P : ℝ}
    (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
    (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)
    {N : ℕ} (q : E) (v : Fin N → E) (t : ℝ)
    (d : FlowForcingChoice N) (i : Fin (d.1.length + 1)) :
    Function.Periodic (canonicalFlowForcingFactors J hΘ q v t d i) P := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact flowSelectedSpeedCoefficient_periodic J hGp hΘp d.1 d.2 q v t
  · exact flowSelectedLowerFactor_periodic hΘ hΘp d.1 d.2 q v t j

end CanonicalFactors

section CircleEstimate

variable {G Θ : E × PolarPoint → ℝ} {P : ℝ} [Fact (0 < P)]
  (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
  (hΘ : ContDiff ℝ ∞ Θ)
  (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
  (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)

/-- The canonical circle descent of each actual forcing factor. -/
def canonicalFlowForcingFactorJet {N : ℕ} (q : E) (v : Fin N → E)
    (t : ℝ) (d : FlowForcingChoice N) (i : Fin (d.1.length + 1))
    (b : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (canonicalFlowForcingFactors J hΘ q v t d i)
    (canonicalFlowForcingFactors_periodic J hΘ hGp hΘp q v t d i)
    (contDiff_canonicalFlowForcingFactors J hΘ hG q v t d i) b

/-- Exactly one factor has order s; every other factor has order one. -/
def canonicalFlowForcingSobolevMajorant {N : ℕ} (q : E)
    (v : Fin N → E) (t : ℝ) (s : ℕ) : ℝ :=
  (2 : ℝ) ^ (s + 1) *
    ∑ d : FlowForcingChoice N, circleProductSobolevConstant P d.1.length s *
      ∑ j : Fin (d.1.length + 1),
        circleRealSobolevNorm (s : ℝ)
          (canonicalFlowForcingFactorJet hG J hΘ hGp hΘp q v t d j 0) *
        ∏ i ∈ Finset.univ.erase j,
          circleRealSobolevNorm 1
            (canonicalFlowForcingFactorJet hG J hΘ hGp hΘp q v t d i 0)

end CircleEstimate

end ForcingAlgebra

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

/-- This is an estimate of the forcing of the actual flow variation
data. Smoothness and periodicity of all selected factors are derived
above, so neither is an additional premise of this estimate. -/
theorem flowParameterCircleVariationData_forcingNorm_le
    (b : ℝ) (n : ℕ) (q : E) (v : Fin (n + 1) → E) (t : ℝ) (s : ℕ) :
    (flowParameterCircleVariationData hG J hΘ hinit hflow hGp hΘp b n q v).forcingNorm s t ≤
      canonicalFlowForcingSobolevMajorant hG J
        (contDiff_globalCircleVectorFlow hG hΘ hinit hflow) hGp hΘp q v t s := by
  let hs := contDiff_globalCircleVectorFlow hG hΘ hinit hflow
  let B := fun α k (_ : k < n + 1) =>
    canonicalFlowVariation (contDiff_flowInitialSlice hs α) k
  have hp := canonicalFlowForcingFactors_periodic J hs hGp hΘp q v t
  have hf := contDiff_canonicalFlowForcingFactors J hs hG q v t
  have he :
      (flowParameterCircleVariationData hG J hΘ hinit hflow hGp hΘp b n q v).forcing t 0 =
        truncatedFlowForcingCircleJet J (flowInitialSlice Θ) B (q, t) v hp hf 0 := by
    ext θ
    induction θ using QuotientAddGroup.induction_on
    rename_i α
    change circleFlowSpeedJet (flowVariationForcing J hs (n + 1) q v)
      (contDiff_flowVariationForcing hG J hs (Nat.succ_pos n) q v)
      (flowVariationForcing_periodic hG J hs hGp hΘp n q v) t 0
        (α : AddCircle P) = _
    simp only [circleFlowSpeedJet_coe_apply, truncatedFlowForcingCircleJet,
      periodicCircleJet_coe_apply, iteratedDeriv_zero]
    rfl
  change circleRealSobolevNorm (s : ℝ)
    ((flowParameterCircleVariationData hG J hΘ hinit hflow hGp hΘp b n q v).forcing t 0) ≤ _
  rw [he]
  exact truncatedFlowForcing_sobolev_le J (flowInitialSlice Θ) B (q, t) v hp hf s

end CircleData

end ContinuousFlexibility.Analysis
