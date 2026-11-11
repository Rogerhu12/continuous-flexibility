import ContinuousFlexibility.Analysis.N01HeightLineResponse

/-!
# The full optical response is bounded by the actual height-direction norm

The mixed N01 tower is first used at interior partial-return radii.
Continuity of the actual response primitive then passes the same bound
to the terminal radius. A direction agreeing locally with a radial
primitive detects at least the full optical travel.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem stateGrading_heightOnlyDirection (S : PhysicalSpacesData)
    (s : ℕ) (η : HeightPair S) :
    stateGrading S s ((η, 0) : AnnularState S) = heightPairGrading S s η := by
  rw [stateGrading, pairGrading_apply]
  have hz : pairGrading realGrading
      (pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading) s
      (0 : ℝ × (CircleSpace S × CircleSpace S)) = 0 :=
    (pairGrading realGrading
      (pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading) s).map_zero'
  rw [hz, add_zero]

theorem heightSpeedVariation_congr_of_eventuallyEq
    {w : ℝ → ℝ} {η ζ : PolarPoint → ℝ} {p : PolarPoint}
    (hη : η =ᶠ[𝓝 p] ζ) :
    heightSpeedVariation w η p = heightSpeedVariation w ζ p := by
  have hdf : fderiv ℝ η =ᶠ[𝓝 p] fderiv ℝ ζ := hη.fderiv
  have hk : heightRadial η p = heightRadial ζ p := by
    change (fderiv ℝ η p) (1, 0) = (fderiv ℝ ζ p) (1, 0)
    rw [hη.fderiv_eq]
  have hp : heightAngular η =ᶠ[𝓝 p] heightAngular ζ := by
    filter_upwards [hdf] with q hq
    change (fderiv ℝ η q) (0, 1) / q.1 = (fderiv ℝ ζ q) (0, 1) / q.1
    rw [hq]
  have hpd : fderiv ℝ (heightAngular η) p = fderiv ℝ (heightAngular ζ) p :=
    hp.fderiv_eq
  unfold heightSpeedVariation
  rw [hk]
  unfold angularPartial radialPartial
  rw [hpd]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The same constant controls every full-component response in every
actual height direction. -/
theorem N01Properties.heightResponse_integral_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ η : HeightPair S, ∀ m θ,
      |∫ r in C.left m..C.right m, heightSpeedVariation D.w (heightPairField S η)
        (r, θ - opticalTravel D.w (C.left m) r)| ≤
      B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        (2 * heightPairGrading S base η + heightPairGrading S loss η) := by
  obtain ⟨B, hB, hbound⟩ := hN.minusFlow_state_q_mixed_derivative_bound
  refine ⟨B, hB, fun η m θ => ?_⟩
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hlh : C.left m < C.right m := (hcontrol.1 m).2.1
  have hl : 0 < C.left m := hgeom.1.1.trans (hcontrol.1 m).1
  have hwp : ∀ r ∈ Icc (C.left m) (C.right m), 0 < D.w r := by
    intro r hr
    exact hgeom.1.2.2.2.2.1 r
      ⟨(hcontrol.1 m).1.trans_le hr.1, hr.2.trans_lt (hcontrol.1 m).2.2⟩
  have hη : ContDiff ℝ ∞ (heightPairField S η) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
  let f : ℝ → ℝ := fun r => heightSpeedVariation D.w (heightPairField S η)
    (r, θ - opticalTravel D.w (C.left m) r)
  let G : ℝ → ℝ := fun b => ∫ r in C.left m..b, f r
  have hi : IntervalIntegrable f volume (C.left m) (C.right m) :=
    (heightResponseIntegrand_continuousOn hgeom.1.2.2.1.1 hη hl hlh.le hwp θ)
      .intervalIntegrable_of_Icc hlh.le
  have hGc : ContinuousOn G (Icc (C.left m) (C.right m)) := by
    simpa only [G, uIcc_of_le hlh.le] using
      intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hc : ContinuousOn (fun b => |G b|) (Icc (C.left m) (C.right m)) := hGc.abs
  have hclosure : C.right m ∈ closure (Ioo (C.left m) (C.right m)) := by
    rw [closure_Ioo hlh.ne]
    exact ⟨hlh.le, le_rfl⟩
  haveI : NeBot (𝓝[Ioo (C.left m) (C.right m)] (C.right m)) :=
    mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hlim : Tendsto (fun b => |G b|)
      (𝓝[Ioo (C.left m) (C.right m)] (C.right m)) (𝓝 |G (C.right m)|) :=
    (hc (C.right m) ⟨hlh.le, le_rfl⟩).mono Ioo_subset_Icc_self
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hbi := hbound ((η, 0) : AnnularState S) m b θ hb
  rw [(hN.minusFlow_height_q_mixed_hasDerivAt hS hT η m θ ⟨hb.1.le, hb.2.le⟩).deriv]
    at hbi
  simpa only [stateGrading_heightOnlyDirection] using hbi

/-- Only local agreement on the open component is needed. Turning
endpoints are removed as null singletons when identifying the integral. -/
theorem N01Properties.opticalTravel_le_radialHeightDirection_weight
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ η : HeightPair S, ∀ m (h : ℝ → ℝ),
      (∀ r, HasDerivAt h (D.w r) r) →
      (∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
        heightPairField S η =ᶠ[𝓝 (r, θ)] Radial.radialHeightField h) →
      C.travel m ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          (2 * heightPairGrading S base η + heightPairGrading S loss η) := by
  obtain ⟨B, hB, hbound⟩ := hN.heightResponse_integral_bound hS hT
  refine ⟨B, hB, fun η m h hhw hgerm => ?_⟩
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hlh : C.left m < C.right m := (hcontrol.1 m).2.1
  have hl : 0 < C.left m := hgeom.1.1.trans (hcontrol.1 m).1
  have hwp : ∀ r ∈ Icc (C.left m) (C.right m), 0 < D.w r := by
    intro r hr
    exact hgeom.1.2.2.2.2.1 r
      ⟨(hcontrol.1 m).1.trans_le hr.1, hr.2.trans_lt (hcontrol.1 m).2.2⟩
  let f : ℝ → ℝ := fun r => heightSpeedVariation D.w (heightPairField S η)
    (r, (0 : ℝ) - opticalTravel D.w (C.left m) r)
  have hresponse : (∫ r in C.left m..C.right m, f r) =
      ∫ r in C.left m..C.right m, (1 + D.w r ^ 2) * opticalSpeed D.w r := by
    apply intervalIntegral.integral_congr_ae
    apply ae_uIoc_imp_of_forall_Ioo hlh.le
    intro r hr
    change heightSpeedVariation D.w (heightPairField S η)
      (r, (0 : ℝ) - opticalTravel D.w (C.left m) r) = _
    rw [heightSpeedVariation_congr_of_eventuallyEq
      (hgerm r hr ((0 : ℝ) - opticalTravel D.w (C.left m) r)),
      heightSpeedVariation_radialHeightField hhw (hwp r ⟨hr.1.le, hr.2.le⟩).ne']
    rfl
  have hcO := continuousOn_opticalSpeed_of_profile hgeom.1.2.2.1.1 hl hwp
  have hiO : IntervalIntegrable (opticalSpeed D.w) volume (C.left m) (C.right m) :=
    hcO.intervalIntegrable_of_Icc hlh.le
  have hcE : ContinuousOn (fun r => (1 + D.w r ^ 2) * opticalSpeed D.w r)
      (Icc (C.left m) (C.right m)) :=
    (continuous_const.add (hgeom.1.2.2.1.1.continuous.pow 2)).continuousOn.mul hcO
  have hiE : IntervalIntegrable (fun r => (1 + D.w r ^ 2) * opticalSpeed D.w r)
      volume (C.left m) (C.right m) := hcE.intervalIntegrable_of_Icc hlh.le
  have htravel : C.travel m = ∫ r in C.left m..C.right m, opticalSpeed D.w r :=
    hcontrol.2.2.2.2.2.2.2.1 m
  have hbi := hbound η m 0
  change |∫ r in C.left m..C.right m, f r| ≤ _ at hbi
  rw [hresponse] at hbi
  calc
    C.travel m = ∫ r in C.left m..C.right m, opticalSpeed D.w r := htravel
    _ ≤ ∫ r in C.left m..C.right m, (1 + D.w r ^ 2) * opticalSpeed D.w r := by
      apply intervalIntegral.integral_mono_on hlh.le hiO hiE
      intro r hr
      have ho : 0 ≤ opticalSpeed D.w r := Real.sqrt_nonneg _
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg (D.w r))) ho
    _ ≤ |∫ r in C.left m..C.right m, (1 + D.w r ^ 2) * opticalSpeed D.w r| :=
      le_abs_self _
    _ ≤ _ := hbi

end ContinuousFlexibility.Statements
