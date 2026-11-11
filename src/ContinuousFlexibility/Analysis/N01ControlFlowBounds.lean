import ContinuousFlexibility.Analysis.N01ControlCoefficientVariation
import ContinuousFlexibility.Analysis.OpticalControlFullCurvature
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Optical curvature bounds from the actual N01 flow tower

The prescribed flow on a singleton kappa line is identified with partial
optical travel. Its second scalar derivative is the genuine second jet
from N01. The bound is uniform in the radial point and therefore extends
to the full travel by continuity of the curvature integral.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance n01ControlFlowBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01ControlFlowBoundsRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

private theorem drop_zero_power_factor {a b c : ℝ} (h : c ^ (0 : ℕ) * a ≤ b) : a ≤ b := by
  simpa only [pow_zero, one_mul] using h

private theorem oneHigh_at_zero_offset
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base loss : ℕ) (x : E) {k : ℕ} (v : Fin k → E) :
    oneHighVariationWeight p base (0 + loss) (x - x) v =
      oneHighVariationWeight p base loss 0 v :=
  congrArg₂ (fun n y => oneHighVariationWeight p base n y v)
    (Nat.zero_add loss) (sub_self x)

theorem abs_second_deriv_le_of_smoothDirections_germ
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f)
    (x w : E) (hx : x ∈ U) (F : ℝ → ℝ) (c K : ℝ)
    (hgerm : (fun t : ℝ => f (x + t • w)) =ᶠ[𝓝 (0 : ℝ)] (fun t => c - F t))
    (hbound : |J.D 2 x (fun _ => w)| ≤ K) :
    |deriv (deriv F) 0| ≤ K := by
  have hd := Filter.EventuallyEq.iteratedDeriv_eq 2 hgerm
  rw [iteratedDeriv_const_sub (by norm_num : 0 < (2 : ℕ)) c,
    iteratedDeriv_neg] at hd
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hd
  have hj : J.D 2 x (fun _ => w) = -deriv (deriv F) 0 :=
    (J.deriv_twice_line x w hx).symm.trans hd
  simpa only [hj, abs_neg] using hbound

theorem le_at_right_of_continuousOn_closed_interval
    {f : ℝ → ℝ} {a b K : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hb : ∀ r ∈ Ioo a b, f r ≤ K) :
    f b ≤ K := by
  have hclosure : b ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  have : NeBot (𝓝[Ioo a b] b) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hlim : Tendsto f (𝓝[Ioo a b] b) (𝓝 (f b)) :=
    (hc b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hb r hr

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- No derivative at the radial endpoint is assumed: this statement only
uses the interior flow tower that appears verbatim in N01. -/
theorem N01Properties.controlTravelPartial_second_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
      |deriv (deriv (fun t => opticalTravel
        (opticalLogPerturbation D.w (C.control m) t) (C.left m) r)) 0| ≤
      B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          base loss 0 (fun _ : Fin 2 =>
            (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, (0 : ℝ))) := by
  let hdata := hN.2.2.2.2.2.2.2.2.2.2.2.2 2 0
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ (m : ℕ) (r : ℝ), r ∈ Ioo (C.left m) (C.right m) →
      |deriv (deriv (fun t => opticalTravel
        (opticalLogPerturbation D.w (C.control m) t) (C.left m) r)) 0| ≤
      B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          base loss 0 (fun _ : Fin 2 =>
            (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, (0 : ℝ))) := by
    intro m r hr
    let v : AnnularState S × ℝ :=
      (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0)
    let F : ℝ → ℝ := fun t => opticalTravel
      (opticalLogPerturbation D.w (C.control m) t) (C.left m) r
    have hz0 : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
      constructor
      · have hz : stateGrading S base (C.referenceState - C.referenceState) = 0 :=
          (congrArg (fun u : AnnularState S => stateGrading S base u)
            (sub_self C.referenceState)).trans (stateGrading S base).map_zero'
        exact hz.trans_lt hN.2.1
      · simpa only [abs_zero] using hN.2.1
    let htower := hdata.choose_spec.2 m 0 0 (r, 0) (by norm_num) hr
    have hgerm :
        (fun t : ℝ => ordinaryFlowFamily S C m 0 0 (r, 0)
          ((C.referenceState, 0) + t • v)) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => -C.minusFlow (C.referenceState, 0) m r 0 - F t) := by
      have hf := hN.minusFlow_singletonKappaLine hS hT m 0 ⟨hr.1.le, hr.2.le⟩
      filter_upwards [hf] with t ht
      dsimp only [v]
      rw [singletonKappa_joint_line hS]
      simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero]
      rw [ht]
      dsimp only [F]
      ring
    have hb := htower.choose_spec (C.referenceState, 0) hz0 (fun _ : Fin 2 => v)
    have hderiv := abs_second_deriv_le_of_smoothDirections_germ htower.choose
      (C.referenceState, 0) v hz0 F (-C.minusFlow (C.referenceState, 0) m r 0) _ hgerm
      (drop_zero_power_factor hb)
    exact hderiv.trans_eq (congrArg
      (fun W : ℝ => B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B * W)
      (oneHigh_at_zero_offset (pairGrading (stateGrading S) realGrading)
        base loss (C.referenceState, (0 : ℝ)) (fun _ : Fin 2 => v)))
  exact Exists.intro B (And.intro hB hpoint)

/-- The same fixed ratio on the full closed component gives the actual
second parameter derivative for every partial interval. -/
theorem N01Properties.controlTravelPartial_hasDerivAt_second
    (hN : N01Properties D T S C base loss ε) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    HasDerivAt (deriv (fun t => opticalTravel
      (opticalLogPerturbation D.w (C.control m) t) (C.left m) r))
      (-(∫ s in C.left m..r,
        opticalSpeed D.w s * opticalLogRatio D.w (C.control m) s ^ 2 / 4)) 0 := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  rcases hcontrol with ⟨hinterval, hturn, _, hneg, _, hcontrols, _⟩
  have hl : 0 < C.left m := hgeom.1.1.trans (hinterval m).1
  have hpos : ∀ s ∈ Icc (C.left m) (C.right m), 0 < D.w s := by
    intro s hs
    exact hgeom.1.2.2.2.2.1 s
      ⟨(hinterval m).1.trans_le hs.1, hs.2.trans_lt (hinterval m).2.2⟩
  have heq : (fun t => opticalTravel
      (opticalLogPerturbation D.w (C.control m) t) (C.left m) r) =
      (fun t => ∫ s in C.left m..r,
        opticalSpeed D.w s * Real.sqrt (1 + t * opticalLogRatio D.w (C.control m) s)) := by
    funext t
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1.le] at hs
    exact opticalSpeed_logPerturbation_factor hl hgeom.1.2.2.1.1 (hcontrols m).1
      hpos (hneg m) ⟨(hturn m).1, (hturn m).2.1⟩ (hcontrols m).2.2
      ⟨hs.1, hs.2.trans hr.2.le⟩
  rw [heq]
  exact (Analysis.hasDerivAt_sqrtFactor_integral_twice hr.1
    ((continuousOn_opticalSpeed_of_profile hgeom.1.2.2.1.1 hl hpos).mono
      (Icc_subset_Icc le_rfl hr.2.le))
    ((continuousOn_opticalLogRatio hgeom.1.2.2.1.1 (hcontrols m).1
      (hneg m) (hturn m) (hcontrols m).2.2).mono
      (Icc_subset_Icc le_rfl hr.2.le))).2

theorem N01Properties.controlCurvaturePrimitive_continuousOn
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    ContinuousOn (fun r => ∫ s in C.left m..r,
      opticalSpeed D.w s * opticalLogRatio D.w (C.control m) s ^ 2 / 4)
      (Icc (C.left m) (C.right m)) := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  rcases hcontrol with ⟨hinterval, hturn, _, hneg, _, hcontrols, _⟩
  have hl : 0 < C.left m := hgeom.1.1.trans (hinterval m).1
  have hpos : ∀ s ∈ Icc (C.left m) (C.right m), 0 < D.w s := by
    intro s hs
    exact hgeom.1.2.2.2.2.1 s
      ⟨(hinterval m).1.trans_le hs.1, hs.2.trans_lt (hinterval m).2.2⟩
  have ha := continuousOn_opticalSpeed_of_profile hgeom.1.2.2.1.1 hl hpos
  have hv := continuousOn_opticalLogRatio hgeom.1.2.2.1.1 (hcontrols m).1
    (hneg m) (hturn m) (hcontrols m).2.2
  have hc : ContinuousOn (fun s => opticalSpeed D.w s *
      opticalLogRatio D.w (C.control m) s ^ 2 / 4)
      (Icc (C.left m) (C.right m)) := by
    exact ((ha.mul (hv.pow 2)).div_const 4).congr (fun _ _ => rfl)
  have hi : IntervalIntegrable (fun s => opticalSpeed D.w s *
      opticalLogRatio D.w (C.control m) s ^ 2 / 4) volume (C.left m) (C.right m) :=
    hc.intervalIntegrable_of_Icc (hinterval m).2.1.le
  simpa only [uIcc_of_le (hinterval m).2.1.le] using
    intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc

/-- The full optical second variation inherits the same uniform bound.
The passage to the endpoint is a limit of the actual curvature primitive. -/
theorem N01Properties.controlTravel_second_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ m,
      |deriv (deriv (fun t => opticalTravel
        (opticalLogPerturbation D.w (C.control m) t) (C.left m) (C.right m))) 0| ≤
      B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          base loss 0 (fun _ : Fin 2 =>
            (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, (0 : ℝ))) := by
  let hdata := hN.controlTravelPartial_second_bound hS hT
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ m : ℕ,
      |deriv (deriv (fun t => opticalTravel
        (opticalLogPerturbation D.w (C.control m) t) (C.left m) (C.right m))) 0| ≤
      B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          base loss 0 (fun _ : Fin 2 =>
            (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, (0 : ℝ))) := by
    intro m
    let K : ℝ := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B *
      oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
        base loss 0 (fun _ : Fin 2 =>
          (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, (0 : ℝ)))
    change |deriv (deriv (fun t => opticalTravel
      (opticalLogPerturbation D.w (C.control m) t) (C.left m) (C.right m))) 0| ≤ K
    have hlh : C.left m < C.right m := (hN.2.2.2.1.1 m).2.1
    let G (r : ℝ) : ℝ := ∫ s in C.left m..r,
      opticalSpeed D.w s * opticalLogRatio D.w (C.control m) s ^ 2 / 4
    have hc : ContinuousOn (fun r => |G r|) (Icc (C.left m) (C.right m)) :=
      (hN.controlCurvaturePrimitive_continuousOn m).abs
    have hinner : ∀ r ∈ Ioo (C.left m) (C.right m), |G r| ≤ K := by
      intro r hr
      have heq : |deriv (deriv (fun t => opticalTravel
          (opticalLogPerturbation D.w (C.control m) t) (C.left m) r)) 0| = |G r| := by
        simpa only [G, abs_neg] using
          congrArg abs (hN.controlTravelPartial_hasDerivAt_second m hr).deriv
      exact heq.symm.trans_le (hdata.choose_spec.2 m r hr)
    have hend : |deriv (deriv (fun t => opticalTravel
        (opticalLogPerturbation D.w (C.control m) t) (C.left m) (C.right m))) 0| =
        |G (C.right m)| := by
      simpa only [G, abs_neg] using congrArg abs (hN.controlTravel_hasDerivAt_second m).deriv
    exact hend.trans_le (le_at_right_of_continuousOn_closed_interval
      (f := fun r => |G r|) (a := C.left m) (b := C.right m) (K := K) hlh hc hinner)
  exact Exists.intro B (And.intro hB hpoint)

end ContinuousFlexibility.Statements
