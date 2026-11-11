import ContinuousFlexibility.Radial.SeedPureTail
import ContinuousFlexibility.Radial.ConeModeCutoff
import ContinuousFlexibility.Radial.SeedOrientedGluing
import ContinuousFlexibility.Radial.SeedConnectorReconstruction

/-!
# Continuing a mixed cone tail to a pure cone mode

The new connector agrees with the actual cone solution on a full germ
at an inward point where that solution is nonzero.  Its profile is
strictly increasing everywhere.  An oriented germ splice therefore
preserves the outward natural tail and all its simple critical points.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def seedConeFrequency (right : Bool) : ℝ := if right then -2 else 2

theorem seedConeFrequency_sq (right : Bool) : seedConeFrequency right ^ 2 = 4 := by
  cases right <;> norm_num [seedConeFrequency]

theorem seedConeFrequency_ne_zero (right : Bool) : seedConeFrequency right ≠ 0 := by
  cases right <;> norm_num [seedConeFrequency]

theorem seedConeFrequency_order (right : Bool) (x y : ℝ) :
    seedConeFrequency right * x < seedConeFrequency right * y ↔
      (if right then y < x else x < y) := by
  cases right <;> dsimp only [seedConeFrequency] <;> constructor <;> intro h <;> linarith

theorem seedConeFrequency_log_order (right : Bool) {c r : ℝ}
    (hc : 0 < c) (hr : 0 < r) :
    seedConeFrequency right * log c < seedConeFrequency right * log r ↔
      (if right then r < c else c < r) := by
  rw [seedConeFrequency_order]
  cases right with
  | false => exact log_lt_log_iff hc hr
  | true => exact log_lt_log_iff hr hc

private theorem signedHalfLine_preconnected (s q : ℝ) :
    IsPreconnected {y : ℝ | q < s * y} := by
  apply Set.OrdConnected.isPreconnected
  constructor
  intro x hx y hy z hz
  rcases le_total 0 s with hs | hs
  · exact hx.trans_le (mul_le_mul_of_nonneg_left hz.1 hs)
  · exact hy.trans_le (mul_le_mul_of_nonpos_left hz.2 hs)

private theorem radial_modes_at_exp (A B y : ℝ) :
    A * exp y ^ 2 + B / exp y ^ 2 = coneModePair 2 A B y := by
  have hp : exp y ^ 2 = exp (2 * y) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hn : (exp (2 * y))⁻¹ = exp (-2 * y) := by
    rw [← exp_neg]
    congr 1
    ring
  simp only [coneModePair, hp, div_eq_mul_inv, hn]

private theorem radialJacobi_height_mul (a A r : ℝ) (w u : ℝ → ℝ) :
    radialJacobi a w (fun x => A * u x) r = A * radialJacobi a w u r := by
  have hflux : (fun x => w x * deriv (fun t => A * u t) x) =
      fun x => A * (w x * deriv u x) := by
    funext x
    rw [deriv_const_mul_field]
    ring
  unfold radialJacobi
  rw [hflux, deriv_const_mul_field]
  ring

theorem connectorProfile_eq_cone_on_const {k : ℝ → ℝ} {J : Set ℝ} {p : ℝ}
    (hk : ContDiff ℝ ∞ k) (hk4 : ∀ y, k y < 4)
    (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hka : EqOn k (fun _ => p) J) (hp : p ^ 2 = 4)
    (y₀ f₀ : ℝ) {y₃ r : ℝ} (hy₃ : y₃ ∈ J) (hr : log r ∈ J) :
    connectorProfile k y₀ f₀ r =
      exp (connectorLogProfile k y₀ f₀ y₃) * r := by
  have hz (y : ℝ) (hy : y ∈ J) : connectorSlope k y = 0 := by
    have hg : k =ᶠ[𝓝 y] fun _ => p :=
      Filter.eventuallyEq_of_mem (hJ.mem_nhds hy) (fun t ht => hka ht)
    rw [connectorSlope, hg.eq_of_nhds, hg.deriv_eq, deriv_const, hp]
    simp only [add_zero, sub_self, zero_div]
  have he : connectorLogProfile k y₀ f₀ (log r) =
      connectorLogProfile k y₀ f₀ y₃ :=
    hJ.is_const_of_deriv_eq_zero hconn
      (fun y _ => (hasDerivAt_connectorLogProfile hk hk4 y₀ f₀ y).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [(hasDerivAt_connectorLogProfile hk hk4 y₀ f₀ y).deriv, hz y hy])
      hr hy₃
  rw [connectorProfile, he, mul_comm]

/-- Every actual mixed cone tail admits an inward pure-mode continuation.
The original natural tail, endpoint and critical points are retained. -/
theorem SeedConeTail.toPureTail {D : ReferenceData} {right : Bool} {entry : ℝ} {u : ℝ → ℝ}
    (T : SeedConeTail D right entry u) (hentry : entry ∈ radialCore D) :
    Nonempty (SeedPureTail D right entry u) := by
  let s : ℝ := seedConeFrequency right
  let A : ℝ := if right then T.coneB else T.coneA
  let B : ℝ := if right then T.coneA else T.coneB
  let Q : ℝ := s * log T.cut
  have hs : s ^ 2 = 4 := seedConeFrequency_sq right
  have hsne : s ≠ 0 := seedConeFrequency_ne_zero right
  have hAB : (A, B) ≠ (0, 0) := by
    cases right <;> simpa only [A, B, Prod.mk.injEq, and_comm] using T.coeff_ne_zero
  have hPair : coneModePair s A B = coneModePair 2 T.coneA T.coneB := by
    cases right with
    | false => rfl
    | true => exact coneModePair_neg_swap 2 T.coneA T.coneB
  obtain ⟨P⟩ := exists_coneModeCutoff (Q := Q) hs hAB
  let r₀ : ℝ := exp P.base
  let r₃ : ℝ := exp (P.stop / s)
  have hr₀ : 0 < r₀ := exp_pos _
  have hr₃ : 0 < r₃ := exp_pos _
  have hsStop : s * (P.stop / s) = P.stop := by field_simp [hsne]
  have hinward (y : ℝ) (hy : Q < s * y) :
      (if right then exp y < T.cut else T.cut < exp y) := by
    apply (seedConeFrequency_log_order right T.cut_pos (exp_pos y)).mp
    simpa only [log_exp, Q, s] using hy
  have hdomain (r : ℝ) (hr : 0 < r)
      (hi : if right then r < T.cut else T.cut < r) :
      r ∈ seedConeTailDomain D right := by
    cases right with
    | false => exact hentry.1.trans (T.cut_order.trans hi)
    | true => exact ⟨hr, hi.trans (T.cut_order.trans hentry.2)⟩
  have hcone (y : ℝ) (hy : Q < s * y) :
      T.height (exp y) = coneModePair s A B y := by
    have h := (T.cone_eq (exp y) (exp_pos y) (hinward y hy)).2
    rw [hPair]
    exact h.trans (radial_modes_at_exp T.coneA T.coneB y)
  have hr₀cut : if right then r₀ < T.cut else T.cut < r₀ :=
    hinward P.base P.base_deep
  have hr₀entry : if right then r₀ < entry else entry < r₀ := by
    cases right with
    | false => exact T.cut_order.trans hr₀cut
    | true => exact hr₀cut.trans T.cut_order
  have hr₃r₀ : if right then r₃ < r₀ else r₀ < r₃ := by
    apply (seedConeFrequency_log_order right hr₀ hr₃).mp
    change s * log (exp P.base) < s * log (exp (P.stop / s))
    rw [log_exp, log_exp, hsStop]
    exact P.stop_after
  have hr₃entry : if right then r₃ < entry else entry < r₃ := by
    cases right with
    | false => exact hr₀entry.trans hr₃r₀
    | true => exact hr₃r₀.trans hr₀entry
  have hcoord : Continuous (fun y : ℝ => s * y) := continuous_const.mul continuous_id
  have hlogGerm : coneLogPullback T.height =ᶠ[𝓝 P.base] coneModePair s A B := by
    filter_upwards [(isOpen_Ioi.preimage hcoord).mem_nhds P.base_deep] with y hy
    exact hcone y hy
  have hHeightAt (y : ℝ) : ContDiffAt ℝ ∞ T.height (exp y) :=
    T.height_smooth.contDiffAt (Ioi_mem_nhds (exp_pos y))
  have hProfileAt (y : ℝ) : ContDiffAt ℝ ∞ T.profile (exp y) :=
    T.profile_smooth.contDiffAt (Ioi_mem_nhds (exp_pos y))
  have hactualSlope :
      (fun y => deriv (coneModePair s A B) y / coneModePair s A B y) =ᶠ[𝓝 P.base]
        seedLogSlope T.height := by
    filter_upwards [hlogGerm, hlogGerm.deriv] with y hv hdv
    rw [← hv, ← hdv,
      (hasDerivAt_coneLogPullback ((hHeightAt y).differentiableAt (by simp))).deriv]
    rfl
  have hSlopeGerm : P.slope =ᶠ[𝓝 P.base] seedLogSlope T.height :=
    P.slope_germ.trans hactualSlope
  have hModeSmooth : ContDiff ℝ ∞ (coneModePair s A B) := by
    unfold coneModePair
    fun_prop
  have hnonzero : T.height r₀ ≠ 0 := by
    change T.height (exp P.base) ≠ 0
    rw [hcone P.base P.base_deep]
    exact P.base_nonzero
  have hlocal : ∀ᶠ y in 𝓝 P.base,
      Q < s * y ∧ T.height (exp y) ≠ 0 ∧ P.slope y = seedLogSlope T.height y := by
    filter_upwards [(isOpen_Ioi.preimage hcoord).mem_nhds P.base_deep,
      (isOpen_ne hModeSmooth.continuous continuous_const).mem_nhds P.base_nonzero,
      hSlopeGerm] with y hy hn hk
    exact ⟨hy, by rw [hcone y hy]; exact hn, hk⟩
  obtain ⟨l, h, hbase, hJ⟩ := hlocal.exists_Ioo_subset
  have hJdomain (y : ℝ) (hy : y ∈ Ioo l h) : exp y ∈ seedConeTailDomain D right :=
    hdomain (exp y) (exp_pos y) (hinward y (hJ hy).1)
  let f₀ : ℝ := log (T.profile r₀) - P.base
  let W : ℝ → ℝ := connectorProfile P.slope P.base f₀
  let U : ℝ → ℝ := fun r => T.height r₀ * connectorHeight P.slope P.base 0 r
  have hWg : W =ᶠ[𝓝 r₀] T.profile :=
    connectorProfile_reconstruct_germ P.smooth P.below_four isOpen_Ioo
      (convex_Ioo l h).isPreconnected hbase
      (fun y _ => (hProfileAt y).differentiableAt (by simp))
      (fun y _ => (hHeightAt y).differentiableAt (by simp))
      (fun y _ => ((hHeightAt y).derivWithin (m := ∞) (by simp)).differentiableAt (by simp))
      (fun y hy => T.positive _ (hJdomain y hy))
      (fun y hy => (hJ hy).2.1)
      (fun y hy => T.homogeneous _ (hJdomain y hy))
      (fun _ hy => (hJ hy).2.2)
  have hUg : U =ᶠ[𝓝 r₀] T.height :=
    connectorHeight_reconstruct_germ P.smooth isOpen_Ioo
      (convex_Ioo l h).isPreconnected hbase
      (fun y _ => (hHeightAt y).differentiableAt (by simp))
      (fun y hy => (hJ hy).2.1) (fun _ hy => (hJ hy).2.2)
  have hWsmooth : ContDiffOn ℝ ∞ W (Ioi 0) :=
    connectorProfile_contDiffOn P.smooth P.below_four _ _
  have hUsmooth : ContDiffOn ℝ ∞ U (Ioi 0) :=
    contDiffOn_const.mul (connectorHeight_contDiffOn P.smooth _ _)
  have hWpos (r : ℝ) (hr : 0 < r) : 0 < W r :=
    connectorProfile_pos _ _ _ hr
  have hWdpos (r : ℝ) (hr : 0 < r) : 0 < deriv W r := by
    change 0 < deriv (connectorProfile P.slope P.base f₀) r
    rw [(hasDerivAt_connectorProfile P.smooth P.below_four P.base f₀ hr).deriv]
    exact mul_pos (exp_pos _)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (P.positive (log r)))
  have hEquation (r : ℝ) (hr : 0 < r) : radialJacobi 4 W U r = 0 := by
    change radialJacobi 4 (connectorProfile P.slope P.base f₀)
      (fun x => T.height r₀ * connectorHeight P.slope P.base 0 x) r = 0
    rw [radialJacobi_height_mul, radialJacobi_connector P.smooth P.below_four P.base f₀ 0 hr,
      mul_zero]
  let J : Set ℝ := {y | P.stop < s * y}
  have hJopen : IsOpen J := isOpen_Ioi.preimage hcoord
  have hJconn : IsPreconnected J := signedHalfLine_preconnected s P.stop
  let y₄ : ℝ := (P.stop + 1) / s
  have hy₄ : y₄ ∈ J := by
    change P.stop < s * ((P.stop + 1) / s)
    have hcancel : s * ((P.stop + 1) / s) = P.stop + 1 := by field_simp [hsne]
    rw [hcancel]
    linarith
  have hconst : EqOn P.slope (fun _ => P.mode) J := fun y hy => P.pure y hy.le
  let C₁ : ℝ := exp (connectorLogProfile P.slope P.base f₀ y₄)
  let A₁ : ℝ := T.height r₀ * exp (connectorLogHeight P.slope P.base 0 y₄ - P.mode * y₄)
  have hC₁ : 0 < C₁ := exp_pos _
  have hA₁ : A₁ ≠ 0 := mul_ne_zero hnonzero (exp_pos _).ne'
  have hPure (r : ℝ) (hr : 0 < r)
      (hi : if right then r < r₃ else r₃ < r) :
      W r = C₁ * r ∧ U r = A₁ * r ^ P.mode := by
    have hlog : log r ∈ J := by
      have h := (seedConeFrequency_log_order right hr₃ hr).mpr hi
      change s * log (exp (P.stop / s)) < s * log r at h
      rw [log_exp, hsStop] at h
      exact h
    refine ⟨connectorProfile_eq_cone_on_const P.smooth P.below_four hJopen hJconn
      hconst P.mode_sq P.base f₀ hy₄ hlog, ?_⟩
    dsimp only [U, A₁]
    rw [connectorHeight_eq_power_of_const P.smooth hJopen hJconn hconst
      P.base 0 hy₄ hr hlog]
    ring
  let W₁ : ℝ → ℝ := seedOrientedGlue right r₀ W T.profile
  let U₁ : ℝ → ℝ := seedOrientedGlue right r₀ U T.height
  have hin (r : ℝ) (hr : if right then r ≤ r₀ else r₀ ≤ r) :
      W₁ =ᶠ[𝓝 r] W ∧ U₁ =ᶠ[𝓝 r] U :=
    ⟨seedOrientedGlue_inward_germ hWg hr, seedOrientedGlue_inward_germ hUg hr⟩
  have hout (r : ℝ) (hr : if right then r₀ ≤ r else r ≤ r₀) :
      W₁ =ᶠ[𝓝 r] T.profile ∧ U₁ =ᶠ[𝓝 r] T.height :=
    ⟨seedOrientedGlue_outward_germ hWg hr, seedOrientedGlue_outward_germ hUg hr⟩
  have hinpos (r : ℝ) (hd : r ∈ seedConeTailDomain D right)
      (hi : if right then r ≤ r₀ else r₀ ≤ r) : 0 < r := by
    cases right with
    | false => exact hr₀.trans_le hi
    | true => exact hd.1
  refine ⟨{
    profile := W₁
    height := U₁
    profile_smooth := contDiffOn_seedOrientedGlue hWsmooth T.profile_smooth hWg
    height_smooth := contDiffOn_seedOrientedGlue hUsmooth T.height_smooth hUg
    outward_zero := ?_
    tail_eq := ?_
    positive := ?_
    simple_critical := ?_
    homogeneous := ?_
    cut := r₃
    cut_pos := hr₃
    cut_order := hr₃entry
    cone_scale := C₁
    amplitude := A₁
    mode := P.mode
    scale_pos := hC₁
    amplitude_ne_zero := hA₁
    mode_sq := P.mode_sq
    pure_eq := ?_ }⟩
  · intro r hr
    have hs : if right then r₀ ≤ r else r ≤ r₀ := by
      cases right with
      | false => exact hr.trans (hentry.1.trans hr₀entry).le
      | true => exact (hr₀entry.trans hentry.2).le.trans hr
    rw [(hout r hs).1.eq_of_nhds, (hout r hs).2.eq_of_nhds]
    exact T.outward_zero r hr
  · intro r hr
    have hs : if right then r₀ ≤ r else r ≤ r₀ := by
      cases right with
      | false => exact (hr.2.trans hr₀entry).le
      | true => exact (hr₀entry.trans hr.1).le
    rw [(hout r hs).1.eq_of_nhds, (hout r hs).2.eq_of_nhds]
    exact T.tail_eq r hr
  · intro r hr
    rcases seedOrientedGlue_sides right r₀ r with hi | ho
    · rw [(hin r hi).1.eq_of_nhds]
      exact hWpos r (hinpos r hr hi)
    · rw [(hout r ho).1.eq_of_nhds]
      exact T.positive r hr
  · intro r hr hd
    rcases seedOrientedGlue_sides right r₀ r with hi | ho
    · have hg := (hin r hi).1
      have he : deriv W r = 0 := hg.deriv_eq.symm.trans hd
      exact False.elim ((hWdpos r (hinpos r hr hi)).ne' he)
    · have hg := (hout r ho).1
      rw [hg.deriv.deriv_eq]
      exact T.simple_critical r hr (hg.deriv_eq.symm.trans hd)
  · intro r hr
    rcases seedOrientedGlue_sides right r₀ r with hi | ho
    · rw [radialJacobi_eq_of_germs (hin r hi).1 (hin r hi).2]
      exact hEquation r (hinpos r hr hi)
    · rw [radialJacobi_eq_of_germs (hout r ho).1 (hout r ho).2]
      exact T.homogeneous r hr
  · intro r hr hi
    have hi₀ : if right then r ≤ r₀ else r₀ ≤ r := by
      cases right with
      | false => exact (hr₃r₀.trans hi).le
      | true => exact (hi.trans hr₃r₀).le
    rw [(hin r hi₀).1.eq_of_nhds, (hin r hi₀).2.eq_of_nhds]
    exact hPure r hr hi

end ContinuousFlexibility.Radial
