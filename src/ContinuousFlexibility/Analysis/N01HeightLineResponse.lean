import ContinuousFlexibility.Analysis.N01FlowHeightResponse
import ContinuousFlexibility.Analysis.N01FlowMixedParameterBound

/-!
# Mixed response on an actual height-only state line

A height-only direction leaves the controlled profile and the sector
coordinates fixed. The actual first q response is linear in that height.
Its ordinary state derivative is therefore the integral of the height
direction's characteristic response, at every partial-return radius.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01HeightLineResponseStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01HeightLineResponseRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem heightOnlyLine_tail (S : PhysicalSpacesData)
    (x : AnnularState S) (η : HeightPair S) (t : ℝ) :
    (x + t • ((η, 0) : AnnularState S)).2 = x.2 := by
  change x.2 + t • (0 : ℝ × (CircleSpace S × CircleSpace S)) = x.2
  simp only [smul_zero, add_zero]

theorem heightOnlyLine_heightFamily (S : PhysicalSpacesData)
    (x : AnnularState S) (η : HeightPair S) (t : ℝ) :
    stateU S (x + t • ((η, 0) : AnnularState S)) =
      heightFamily (stateU S x) (heightPairField S η) t := by
  funext p
  change (S.height (3 / 4 : ℝ)).decode (x.1.1 + t • η.1) p +
      (x.1.2 + t * η.2) * S.chiLeft p.1 =
    ((S.height (3 / 4 : ℝ)).decode x.1.1 p + x.1.2 * S.chiLeft p.1) +
      t * ((S.height (3 / 4 : ℝ)).decode η.1 p + η.2 * S.chiLeft p.1)
  rw [map_add, (S.height (3 / 4 : ℝ)).decode.map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem heightOnlyLine_profile
    (href : referenceStateConditions D S C) (η : HeightPair S) (t : ℝ) :
    stateProfile D S C (C.referenceState + t • ((η, 0) : AnnularState S)) = D.w := by
  funext r
  simp [stateProfile, stateKappa, heightOnlyLine_tail, href.2.2.1,
    href.2.2.2.1, angularMean]

theorem heightOnlyLine_sector
    (href : referenceStateConditions D S C) (η : HeightPair S) (t : ℝ) :
    stateSector S (C.referenceState + t • ((η, 0) : AnnularState S)) := by
  simp only [stateSector, heightOnlyLine_tail, href.2.2.2.1,
    href.2.2.2.2.1, map_zero, Pi.zero_apply, neg_zero]
  exact ⟨fun _ _ _ => True.intro, fun _ _ => True.intro⟩

theorem stateLine_eventually_mem
    (v : AnnularState S) (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (C.referenceState + t • v, 0) ∈ stateNeighborhood S C base ε := by
  have hc : Continuous (fun t : ℝ => |t| * stateGrading S base v) :=
    continuous_abs.mul continuous_const
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * stateGrading S base v < ε :=
    (isOpen_lt hc continuous_const).mem_nhds
      (by simpa only [Set.mem_setOf_eq, abs_zero, zero_mul] using hε)
  filter_upwards [hsmall] with t ht
  constructor
  · simpa only [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs] using ht
  · simpa only [abs_zero] using hε

theorem heightSpeedVariation_continuousAt
    {w : ℝ → ℝ} {η : PolarPoint → ℝ} (hw : ContDiff ℝ ∞ w)
    (hη : ContDiff ℝ ∞ η) {p : PolarPoint} (hr : p.1 ≠ 0) (hwp : w p.1 ≠ 0) :
    ContinuousAt (heightSpeedVariation w η) p := by
  have hk : ContDiffAt ℝ ∞ (heightRadial η) p :=
    contDiffAt_heightRadial hη.contDiffAt (by simp)
  have hp : ContDiffAt ℝ ∞ (heightAngular η) p :=
    contDiffAt_heightAngular hη.contDiffAt (by simp) hr
  have hpr : ContDiffAt ℝ ∞ (radialPartial (heightAngular η)) p :=
    contDiffAt_radialPartial hp (by simp)
  have hpθ : ContDiffAt ℝ ∞ (angularPartial (heightAngular η)) p :=
    contDiffAt_angularPartial hp (by simp)
  have hW : ContinuousAt (fun z : PolarPoint => w z.1) p :=
    hw.continuous.continuousAt.comp continuousAt_fst
  have hE : ContinuousAt (profileEnergy w) p := continuousAt_const.add (hW.pow 2)
  have hrad : ContinuousAt (fun r : ℝ => -deriv w r / (r * w r)) p.1 :=
    ((hw.continuous_deriv (by simp)).continuousAt.neg).div
      (continuousAt_id.mul hw.continuous.continuousAt) (mul_ne_zero hr hwp)
  have hopt : ContinuousAt (fun z : PolarPoint => opticalSpeed w z.1) p :=
    (Real.continuous_sqrt.continuousAt.comp hrad).comp continuousAt_fst
  exact (hE.div hW hwp).mul
    ((hopt.mul (hk.continuousAt.add hpθ.continuousAt)).sub hpr.continuousAt)

/-- This continuity includes both turning radii, since the optical speed
is only used as a continuous scalar factor. -/
theorem heightResponseIntegrand_continuousOn
    {w : ℝ → ℝ} {η : PolarPoint → ℝ} {l h : ℝ}
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η)
    (hl : 0 < l) (hlh : l ≤ h) (hwpos : ∀ r ∈ Icc l h, 0 < w r) (θ : ℝ) :
    ContinuousOn
      (fun r => heightSpeedVariation w η (r, θ - opticalTravel w l r)) (Icc l h) := by
  have ho := continuousOn_opticalSpeed_of_profile hw hl hwpos
  have hi : IntervalIntegrable (opticalSpeed w) volume l h :=
    ho.intervalIntegrable_of_Icc hlh
  have ht : ContinuousOn (opticalTravel w l) (Icc l h) := by
    have hc : ContinuousOn (fun b : ℝ => ∫ r in l..b, opticalSpeed w r) (Icc l h) := by
      simpa only [uIcc_of_le hlh] using
        intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
    exact hc.congr (fun _ _ => rfl)
  have hφ : ContinuousOn (fun r => θ - opticalTravel w l r) (Icc l h) :=
    continuousOn_const.sub ht
  intro r hr
  exact (heightSpeedVariation_continuousAt hw hη (hl.trans_le hr.1).ne'
    (hwpos r hr).ne').comp_continuousWithinAt
      (continuousWithinAt_id.prodMk (hφ r hr))

private theorem heightResponseIntegral_heightFamily
    {w : ℝ → ℝ} {u η : PolarPoint → ℝ} {l b : ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hη : ContDiff ℝ ∞ η)
    (hl : 0 < l) (hlb : l ≤ b) (hwpos : ∀ r ∈ Icc l b, 0 < w r) (θ t : ℝ) :
    (∫ r in l..b, heightSpeedVariation w (heightFamily u η t)
      (r, θ - opticalTravel w l r)) =
      (∫ r in l..b, heightSpeedVariation w u (r, θ - opticalTravel w l r)) +
      t * ∫ r in l..b, heightSpeedVariation w η (r, θ - opticalTravel w l r) := by
  have hi0 : IntervalIntegrable
      (fun r => heightSpeedVariation w u (r, θ - opticalTravel w l r)) volume l b :=
    (heightResponseIntegrand_continuousOn hw hu hl hlb hwpos θ).intervalIntegrable_of_Icc hlb
  have hiη : IntervalIntegrable
      (fun r => heightSpeedVariation w η (r, θ - opticalTravel w l r)) volume l b :=
    (heightResponseIntegrand_continuousOn hw hη hl hlb hwpos θ).intervalIntegrable_of_Icc hlb
  calc
    _ = ∫ r in l..b, heightSpeedVariation w u (r, θ - opticalTravel w l r) +
        t * heightSpeedVariation w η (r, θ - opticalTravel w l r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hlb] at hr
      exact heightSpeedVariation_heightFamily hu hη (hl.trans_le hr.1).ne' t
    _ = _ := by
      rw [intervalIntegral.integral_add hi0 (hiη.const_mul t), intervalIntegral.integral_const_mul]

private theorem N01Properties.heightLine_scalar_deriv_formula
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (η : HeightPair S) (t : ℝ)
    (ht : (C.referenceState + t • ((η, 0) : AnnularState S), 0) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) {b : ℝ} (hb : b ∈ Icc (C.left m) (C.right m)) :
    deriv (fun q : ℝ => C.minusFlow
      (C.referenceState + t • ((η, 0) : AnnularState S), q) m b θ) 0 =
      ∫ r in C.left m..b, heightSpeedVariation D.w
        (heightFamily (stateU S C.referenceState) (heightPairField S η) t)
        (r, θ - opticalTravel D.w (C.left m) r) := by
  have href : referenceStateConditions D S C := hN.2.2.1
  have hd := hN.minusFlow_q_zero_partial_height_response_of_physical hS hT ht
    (heightOnlyLine_sector href η t) m θ hb
  let F : (ℝ → ℝ) → (PolarPoint → ℝ) → ℝ := fun w u =>
    ∫ r in C.left m..b, heightSpeedVariation w u (r, θ - opticalTravel w (C.left m) r)
  exact hd.deriv.trans (congrArg₂ F (heightOnlyLine_profile href η t)
    (heightOnlyLine_heightFamily S C.referenceState η t))

private theorem N01Properties.heightLine_scalar_deriv_affine
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (η : HeightPair S) (m : ℕ) (θ t : ℝ)
    (ht : (C.referenceState + t • ((η, 0) : AnnularState S), 0) ∈ stateNeighborhood S C base ε)
    {b : ℝ} (hb : b ∈ Icc (C.left m) (C.right m)) :
    deriv (fun q : ℝ => C.minusFlow
      (C.referenceState + t • ((η, 0) : AnnularState S), q) m b θ) 0 =
      (∫ r in C.left m..b, heightSpeedVariation D.w (stateU S C.referenceState)
        (r, θ - opticalTravel D.w (C.left m) r)) +
      t * ∫ r in C.left m..b, heightSpeedVariation D.w (heightPairField S η)
        (r, θ - opticalTravel D.w (C.left m) r) := by
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hgeom.1.2.2.1.1
  have hu : ContDiff ℝ ∞ (stateU S C.referenceState) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4)
      C.referenceState.1.1 C.referenceState.1.2
  have hη : ContDiff ℝ ∞ (heightPairField S η) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
  have hl : 0 < C.left m := hgeom.1.1.trans (hcontrol.1 m).1
  have hwp : ∀ r ∈ Icc (C.left m) b, 0 < D.w r := by
    intro r hr
    exact hgeom.1.2.2.2.2.1 r
      ⟨(hcontrol.1 m).1.trans_le hr.1,
        (hr.2.trans hb.2).trans_lt (hcontrol.1 m).2.2⟩
  exact (hN.heightLine_scalar_deriv_formula hS hT η t ht m θ hb).trans
    (heightResponseIntegral_heightFamily hw hu hη hl hb.1 hwp θ t)

private theorem N01Properties.heightLine_scalar_deriv_eventually_affine
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (η : HeightPair S) (m : ℕ) (θ : ℝ)
    {b : ℝ} (hb : b ∈ Icc (C.left m) (C.right m)) :
      (fun t : ℝ => deriv (fun q : ℝ =>
        C.minusFlow (C.referenceState + t • ((η, 0) : AnnularState S), q) m b θ) 0)
        =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ =>
          (∫ r in C.left m..b, heightSpeedVariation D.w (stateU S C.referenceState)
            (r, θ - opticalTravel D.w (C.left m) r)) +
          t * ∫ r in C.left m..b, heightSpeedVariation D.w (heightPairField S η)
            (r, θ - opticalTravel D.w (C.left m) r)) := by
  filter_upwards [stateLine_eventually_mem (C := C) (base := base)
    ((η, 0) : AnnularState S) hN.2.1] with t ht
  exact hN.heightLine_scalar_deriv_affine hS hT η m θ t ht hb

private theorem hasDerivAt_of_eventually_affine
    (f : ℝ → ℝ) (I0 Iη : ℝ)
    (heq : f =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => I0 + t * Iη)) :
    HasDerivAt f Iη 0 := by
  have hlin : HasDerivAt (fun t : ℝ => I0 + t * Iη) Iη 0 := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const Iη).const_add I0
  exact hlin.congr_of_eventuallyEq heq

theorem N01Properties.minusFlow_height_q_mixed_hasDerivAt
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (η : HeightPair S) (m : ℕ) (θ : ℝ)
    {b : ℝ} (hb : b ∈ Icc (C.left m) (C.right m)) :
    HasDerivAt
      (fun t : ℝ => deriv (fun q : ℝ =>
        C.minusFlow (C.referenceState + t • ((η, 0) : AnnularState S), q) m b θ) 0)
      (∫ r in C.left m..b, heightSpeedVariation D.w (heightPairField S η)
        (r, θ - opticalTravel D.w (C.left m) r)) 0 :=
  hasDerivAt_of_eventually_affine _ _ _
    (hN.heightLine_scalar_deriv_eventually_affine hS hT η m θ hb)

end ContinuousFlexibility.Statements
