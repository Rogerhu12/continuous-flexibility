import ContinuousFlexibility.Analysis.N01ControlCoefficientVariation
import ContinuousFlexibility.Analysis.OpticalControlFullCurvature
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Optical curvature bounds from the actual N01 flow tower

The prescribed flow on a singleton kappa line is identified with partial
optical travel. Its second scalar derivative is the genuine second jet
from N01. The bound is uniform in the radial point and therefore extends
to the full travel by continuity of the curvature integral.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

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
  have hdata := hN
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hflow⟩
  obtain ⟨B, hB, hbound⟩ := hflow 2 0
  refine ⟨B, hB, fun m r hr => ?_⟩
  let v : AnnularState S × ℝ :=
    (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0)
  let F : ℝ → ℝ := fun t => opticalTravel
    (opticalLogPerturbation D.w (C.control m) t) (C.left m) r
  have hz0 : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · simpa only [sub_self, map_zero] using hN.2.1
    · simpa only [abs_zero] using hN.2.1
  obtain ⟨J, hJ⟩ := hbound m 0 0 (r, 0) (by norm_num) hr
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
  have hd := Filter.EventuallyEq.iteratedDeriv_eq 2 hgerm
  rw [iteratedDeriv_const_sub (by norm_num : 0 < (2 : ℕ))
      (-C.minusFlow (C.referenceState, 0) m r 0), iteratedDeriv_neg] at hd
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hd
  have hj : J.D 2 (C.referenceState, 0) (fun _ => v) =
      -deriv (deriv F) 0 :=
    (J.deriv_twice_line (C.referenceState, 0) v hz0).symm.trans hd
  have hb := hJ (C.referenceState, 0) hz0 (fun _ : Fin 2 => v)
  rw [hj, abs_neg, sub_self] at hb
  simpa only [pow_zero, one_mul, Nat.zero_add, v, F] using hb

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
  have hi := hc.intervalIntegrable_of_Icc (hinterval m).2.1.le
  simpa only [uIcc_of_le (hinterval m).2.1.le] using
    continuousOn_primitive_interval' hi left_mem_uIcc

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
  obtain ⟨B, hB, hbound⟩ := hN.controlTravelPartial_second_bound hS hT
  refine ⟨B, hB, fun m => ?_⟩
  have hlh : C.left m < C.right m := (hN.2.2.2.1.1 m).2.1
  let G (r : ℝ) : ℝ := ∫ s in C.left m..r,
    opticalSpeed D.w s * opticalLogRatio D.w (C.control m) s ^ 2 / 4
  have hc : ContinuousOn (fun r => |G r|) (Icc (C.left m) (C.right m)) :=
    (hN.controlCurvaturePrimitive_continuousOn m).abs
  have hclosure : C.right m ∈ closure (Ioo (C.left m) (C.right m)) := by
    rw [closure_Ioo hlh.ne]
    exact ⟨hlh.le, le_rfl⟩
  haveI : NeBot (𝓝[Ioo (C.left m) (C.right m)] (C.right m)) :=
    mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hlim : Tendsto (fun r => |G r|)
      (𝓝[Ioo (C.left m) (C.right m)] (C.right m)) (𝓝 |G (C.right m)|) :=
    (hc (C.right m) ⟨hlh.le, le_rfl⟩).mono Ioo_subset_Icc_self
  rw [(hN.controlTravel_hasDerivAt_second m).deriv, abs_neg]
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hb := hbound m r hr
  rw [(hN.controlTravelPartial_hasDerivAt_second m hr).deriv, abs_neg] at hb
  exact hb

end ContinuousFlexibility.Statements
