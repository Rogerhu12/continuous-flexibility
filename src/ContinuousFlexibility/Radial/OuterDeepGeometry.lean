import ContinuousFlexibility.Radial.OuterNaturalPhysicalMass
import ContinuousFlexibility.Radial.OuterCoreIntervals

/-!
# Geometry of the actual logarithmic Morse tail

These facts are obtained directly from the realized radius charts and
the positive radial profile. In particular no deep-tail hypothesis is
used to establish positivity, the coordinate range, or the node geometry.
The mass-resistance inequalities remain separate quantitative work.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem outer_contDiff_tailPhysicalRadius (right : Bool) :
    ContDiff ℝ ∞ (tailPhysicalRadius right) := by
  cases right
  · exact contDiff_exp.comp contDiff_neg
  · exact contDiff_exp

theorem outer_contDiff_massLogDensity {D : ReferenceData}
    (hw : ContDiff ℝ ∞ D.w) (j : ℕ) (endpoint : ℝ) (right : Bool) :
    ContDiff ℝ ∞ (outerMassLogDensity D j endpoint right) := by
  have hr := outer_contDiff_tailPhysicalRadius right
  exact (((hr.div_const endpoint).pow (2 * j ^ 2)).mul (hw.comp hr)).div hr
    (fun x => (tailPhysicalRadius_pos right x).ne')

/-- The signed logarithmic half-open interval maps into the actual
radial annulus, including the physical entrance. -/
theorem outer_physicalRadius_mem_core {D : ReferenceData}
    (hD : RadialProfileGeometry D) {entrance : ℝ}
    (he : entrance ∈ radialCore D) (right : Bool) {x : ℝ}
    (hx : x ∈ Ico (tailPhysicalLog right entrance)
      (tailPhysicalLog right (tailPhysicalEndpoint D right))) :
    tailPhysicalRadius right x ∈ radialCore D := by
  have hp : 0 < entrance := hD.1.trans he.1
  cases right with
  | true =>
      change log entrance ≤ x ∧ x < log D.b at hx
      change D.a < exp x ∧ exp x < D.b
      have hl := exp_le_exp.mpr hx.1
      have hr := exp_lt_exp.mpr hx.2
      rw [exp_log hp] at hl
      rw [exp_log (hD.1.trans hD.2.1)] at hr
      exact ⟨he.1.trans_le hl, hr⟩
  | false =>
      change -log entrance ≤ x ∧ x < -log D.a at hx
      change D.a < exp (-x) ∧ exp (-x) < D.b
      have hl := exp_lt_exp.mpr (show log D.a < -x by linarith only [hx.2])
      have hr := exp_le_exp.mpr (show -x ≤ log entrance by linarith only [hx.1])
      rw [exp_log hD.1] at hl
      rw [exp_log hp] at hr
      exact ⟨hl, hr.trans_lt he.2⟩

theorem outer_physicalLog_lt_endpoint {D : ReferenceData}
    (hD : RadialProfileGeometry D) {entrance : ℝ}
    (he : entrance ∈ radialCore D) (right : Bool) :
    tailPhysicalLog right entrance <
      tailPhysicalLog right (tailPhysicalEndpoint D right) := by
  cases right
  · exact neg_lt_neg (log_lt_log hD.1 he.1)
  · exact log_lt_log (hD.1.trans he.1) he.2

/-- Positivity and all-order regularity are properties of the actual
factory, independently of its spectral smallness parameters. -/
theorem morsePhysicalDeepTail_density_geometry {M : MorseChainData}
    {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (right : Bool) (j start : ℕ)
    {entrance : ℝ} (he : entrance ∈ radialCore D) (η K : ℝ) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    T.entrance < T.endpoint ∧ ContDiff ℝ ∞ T.p ∧
      (∀ x ∈ Ico T.entrance T.endpoint,
        tailPhysicalRadius right x ∈ radialCore D ∧ 0 < T.p x) := by
  have hepos : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact h.geometry.1
    · exact h.geometry.1.trans h.geometry.2.1
  refine ⟨outer_physicalLog_lt_endpoint h.geometry he right,
    outer_contDiff_massLogDensity h.geometry.2.2.1.1 j _ right, ?_⟩
  intro x hx
  have hr := outer_physicalRadius_mem_core h.geometry he right hx
  refine ⟨hr, ?_⟩
  change 0 < (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^
    (2 * j ^ 2) * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x
  exact div_pos (mul_pos
    (pow_pos (div_pos (tailPhysicalRadius_pos right x) hepos) _)
    (h.geometry.2.2.2.2.1 _ hr)) (tailPhysicalRadius_pos right x)

/-- The mass endpoints and both retained endpoints lie in the same
strictly increasing physical radius chart. -/
theorem morseRealized_mass_geometry {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (n : ℕ) (hn : M.index ≤ n) :
    M.radius right n (M.leftX right n) ∈ radialCore D ∧
      morseChainMassEnd M right n ∈ radialCore D ∧
      M.radius right n (M.rightX right n) ∈ radialCore D ∧
      M.radius right n (M.leftX right n) < morseChainMassEnd M right n ∧
      morseChainMassEnd M right n < M.radius right n (M.rightX right n) := by
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data right n hn
  have hl := left_mem_Icc.mpr (hlt.trans htr).le
  have ht : morseChainRightTurn M n ∈ Icc (M.leftX right n) (M.rightX right n) :=
    ⟨hlt.le, htr.le⟩
  have hr := right_mem_Icc.mpr (hlt.trans htr).le
  exact ⟨h.radius_mem_core right n hn _ hl, h.radius_mem_core right n hn _ ht,
    h.radius_mem_core right n hn _ hr, h.radius_strictMonoOn right n hn hl ht hlt,
    h.radius_strictMonoOn right n hn ht hr htr⟩

/-- The outward mass intervals have the strict order required by the
deep-tail operator, on both ends of the actual surface. -/
theorem morsePhysicalDeepTail_node_order {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (j start : ℕ) (hstart : M.index ≤ start)
    (entrance η K : ℝ) (k : ℕ) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    T.node k < T.massEnd k ∧ T.massEnd k < T.node (k + 1) := by
  have hn : M.index ≤ start + k := hstart.trans (Nat.le_add_right start k)
  have hn' : M.index ≤ start + k + 1 := hn.trans (Nat.le_succ _)
  have hm := morseRealized_mass_geometry h right (start + k) hn
  have hm' := morseRealized_mass_geometry h right (start + k + 1) hn'
  have hj := h.join_data right (start + k) hn
  cases right with
  | true =>
      have hjord : M.radius true (start + k) (M.rightX true (start + k)) <
          M.radius true (start + k + 1) (M.leftX true (start + k + 1)) := by
        simpa only [hj.2.1, hj.2.2.1, ite_true] using hj.1
      change log (M.radius true (start + k) (M.leftX true (start + k))) <
        log (morseChainMassEnd M true (start + k)) ∧
        log (morseChainMassEnd M true (start + k)) <
          log (M.radius true (start + (k + 1)) (M.leftX true (start + (k + 1))))
      rw [← Nat.add_assoc]
      exact ⟨log_lt_log (h.geometry.1.trans hm.1.1) hm.2.2.2.1,
        log_lt_log (h.geometry.1.trans hm.2.1.1) (hm.2.2.2.2.trans hjord)⟩
  | false =>
      have hjord : M.radius false (start + k + 1) (M.rightX false (start + k + 1)) <
          M.radius false (start + k) (M.leftX false (start + k)) := by
        simpa only [hj.2.1, hj.2.2.1, Bool.false_eq_true, ite_false] using hj.1
      change -log (morseChainMassEnd M false (start + k)) <
        -log (M.radius false (start + k) (M.leftX false (start + k))) ∧
        -log (M.radius false (start + k) (M.leftX false (start + k))) <
          -log (morseChainMassEnd M false (start + (k + 1)))
      rw [← Nat.add_assoc]
      exact ⟨neg_lt_neg (log_lt_log (h.geometry.1.trans hm.1.1) hm.2.2.2.1),
        neg_lt_neg (log_lt_log (h.geometry.1.trans hm'.2.1.1)
          (hm'.2.2.2.2.trans hjord))⟩

theorem morseRealized_massEnd_tendsto {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) :
    Tendsto (morseChainMassEnd M right) atTop
      (𝓝 (tailPhysicalEndpoint D right)) := by
  have hl := (h.2.2.2.2.2.2.1 right).1
  have hr := (h.2.2.2.2.2.2.1 right).2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr
  · filter_upwards [eventually_ge_atTop M.index] with n hn
    exact (morseRealized_mass_geometry h right n hn).2.2.2.1.le
  · filter_upwards [eventually_ge_atTop M.index] with n hn
    exact (morseRealized_mass_geometry h right n hn).2.2.2.2.le

/-- The actual outward nodes accumulate at the declared logarithmic endpoint. -/
theorem morsePhysicalDeepTail_nodes_tendsto {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (j start : ℕ) (entrance η K : ℝ) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    Tendsto T.node atTop (𝓝 T.endpoint) := by
  have hs : Tendsto (fun k : ℕ => start + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat start
  cases right with
  | true =>
      have hr := (h.2.2.2.2.2.2.1 true).1.comp hs
      exact (continuousAt_log (h.geometry.1.trans h.geometry.2.1).ne').tendsto.comp hr
  | false =>
      have hr := (morseRealized_massEnd_tendsto h false).comp hs
      exact ((continuousAt_log h.geometry.1.ne').tendsto.comp hr).neg

/-- The physical entrance beyond the full transition core. The right
core includes its outgoing glue; the left core ends before the initial
resistance edge. -/
def morseOuterDeepEntrance (M : MorseChainData) (right : Bool) (n : ℕ) : ℝ :=
  if right then M.joinRight true n else M.radius false n (M.leftX false n)

theorem morseOuterDeepEntrance_mem_core {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (n : ℕ) (hn : M.index ≤ n) :
    morseOuterDeepEntrance M right n ∈ radialCore D := by
  cases right with
  | false => exact (morseRealized_mass_geometry h false n hn).1
  | true =>
      have hj := (h.join_data true n hn).2.2.1
      change M.joinRight true n ∈ radialCore D
      rw [hj]
      exact (morseRealized_mass_geometry h true (n + 1) (hn.trans (Nat.le_succ n))).1

theorem morsePhysicalDeepTail_right_entrance {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (j n : ℕ) (hn : M.index ≤ n) (η K : ℝ) :
    let T := morsePhysicalDeepTail M D true j (n + 1)
      (morseOuterDeepEntrance M true n) η K
    T.node 0 = T.entrance := by
  change log (M.radius true (n + 1 + 0) (M.leftX true (n + 1 + 0))) =
    log (M.joinRight true n)
  simp only [Nat.add_zero, (h.join_data true n hn).2.2.1, ite_true]

/-- The left initial resistance edge is nonempty, with the actual
next-cell turning point as its first mass entrance. -/
theorem morsePhysicalDeepTail_left_entrance {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (j n : ℕ) (hn : M.index ≤ n) (η K : ℝ) :
    let T := morsePhysicalDeepTail M D false j (n + 1)
      (morseOuterDeepEntrance M false n) η K
    T.entrance < T.node 0 := by
  have hm := morseRealized_mass_geometry h false (n + 1) (hn.trans (Nat.le_succ n))
  have hj := h.join_data false n hn
  have hjord : M.radius false (n + 1) (M.rightX false (n + 1)) <
      M.radius false n (M.leftX false n) := by
    simpa only [hj.2.1, hj.2.2.1, Bool.false_eq_true, ite_false] using hj.1
  change -log (M.radius false n (M.leftX false n)) <
    -log (morseChainMassEnd M false (n + 1 + 0))
  rw [Nat.add_zero]
  exact neg_lt_neg (log_lt_log (h.geometry.1.trans hm.2.1.1)
    (hm.2.2.2.2.trans hjord))

/-- The left initial edge is exactly the original next-cell resistance
interval in increasing physical radius. -/
theorem morseOuterDeepEntrance_left_eq_resistanceEnd {M : MorseChainData}
    {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (n : ℕ) (hn : M.index ≤ n) :
    morseOuterDeepEntrance M false n = morseChainResistanceEnd M false (n + 1) := by
  have hn' : M.index < n + 1 := hn.trans_lt (Nat.lt_succ_self n)
  simp only [morseOuterDeepEntrance, Bool.false_eq_true, ite_false,
    morseChainResistanceEnd, if_pos hn', Nat.add_sub_cancel]
  exact ((h.join_data false n hn).2.2.1).symm

end ContinuousFlexibility.Radial
