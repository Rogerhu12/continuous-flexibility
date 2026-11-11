import ContinuousFlexibility.Radial.MorseSecondModePhysicalRelation
import ContinuousFlexibility.Radial.DeepTailPhysicalLift
import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Transport of a specified physical natural solution

The given radial solution is pulled back through the actual signed
logarithm. Its square density transforms exactly, so the natural L²
condition passes to the deep equation without a new existence assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
open ContinuousFlexibility.Statements

theorem radialProfileGeometry_weight_nonneg {D : ReferenceData}
    (hD : RadialProfileGeometry D) (r : ℝ) : 0 ≤ D.w r := by
  rcases le_or_gt r D.a with h | h
  · rw [hD.2.2.1.2 r (Or.inl h)]
  · rcases le_or_gt D.b r with h' | h'
    · rw [hD.2.2.1.2 r (Or.inr h')]
    · exact (hD.2.2.2.2.1 r ⟨h, h'⟩).le

theorem contDiff_tailPhysicalRadius (right : Bool) :
    ContDiff ℝ ∞ (tailPhysicalRadius right) := by
  cases right
  · exact contDiff_neg.exp
  · exact contDiff_exp

theorem hasDerivAt_tailPhysicalRadius (right : Bool) (x : ℝ) :
    HasDerivAt (tailPhysicalRadius right)
      ((if right then 1 else -1 : ℝ) * tailPhysicalRadius right x) x := by
  cases right
  · simpa only [tailPhysicalRadius, Bool.false_eq_true, ↓reduceIte,
      mul_neg, mul_one, neg_one_mul] using ((hasDerivAt_id x).neg).exp
  · simpa only [tailPhysicalRadius, ↓reduceIte, one_mul] using hasDerivAt_exp x

theorem tailPhysicalRadius_injective (right : Bool) :
    Function.Injective (tailPhysicalRadius right) := by
  intro x y h
  cases right
  · change exp (-x) = exp (-y) at h
    exact neg_injective (exp_injective h)
  · exact exp_injective h

theorem tailPhysicalRadius_abs_signed (right : Bool) (x : ℝ) :
    |(if right then 1 else -1 : ℝ) * tailPhysicalRadius right x| =
      tailPhysicalRadius right x := by
  cases right <;> simp [tailPhysicalRadius, abs_of_pos (exp_pos _)]

/-- The inverse normalized second-mode gauge of the given physical height. -/
def morseSecondModePullback (D : ReferenceData) (right : Bool)
    (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (tailPhysicalEndpoint D right / tailPhysicalRadius right x) ^ 4 *
    u (tailPhysicalRadius right x)

theorem morseSecondModePullback_contDiffAt {D : ReferenceData} {right : Bool}
    {u : ℝ → ℝ} {x : ℝ}
    (hu : ContDiffAt ℝ ∞ u (tailPhysicalRadius right x)) :
    ContDiffAt ℝ ∞ (morseSecondModePullback D right u) x := by
  have hr := contDiff_tailPhysicalRadius right
  have hg : ContDiff ℝ ∞
      (fun y => (tailPhysicalEndpoint D right / tailPhysicalRadius right y) ^ 4) :=
    (contDiff_const.div hr (fun y => (tailPhysicalRadius_pos right y).ne')).pow 4
  exact hg.contDiffAt.mul (hu.comp x hr.contDiffAt)

theorem morseSecondModePullback_relation {D : ReferenceData} (hD : RadialProfileGeometry D)
    (right : Bool) (u : ℝ → ℝ) (x : ℝ) :
    u (tailPhysicalRadius right x) =
      (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
        (((2 : ℕ) : ℝ) ^ 2) * morseSecondModePullback D right u x := by
  have hR := (morseSecondMode_endpoint_pos hD right).ne'
  have hr := (tailPhysicalRadius_pos right x).ne'
  rw [show ((2 : ℕ) : ℝ) ^ 2 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold morseSecondModePullback tailPhysicalEndpoint
  field_simp [hR, hr]
  <;> ring

/-- Exact equality of the square densities, including the factor 12 in
the original radial Hilbert measure. -/
theorem morseSecondModePullback_square_density {D : ReferenceData}
    (hD : RadialProfileGeometry D) (T : MorseChainData) (N : ℕ)
    (right : Bool) (u : ℝ → ℝ) (x : ℝ) :
    (morseSecondModeTail D T N right).p x *
        morseSecondModePullback D right u x ^ 2 =
      (1 / 12 : ℝ) * (tailPhysicalRadius right x *
        (12 * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x ^ 2 *
          u (tailPhysicalRadius right x) ^ 2)) := by
  have hR := (morseSecondMode_endpoint_pos hD right).ne'
  cases right <;>
    simp only [morseSecondModeTail, morseSecondModeDensity, morseSecondModePullback,
      tailPhysicalEndpoint, tailPhysicalRadius, Bool.false_eq_true, ↓reduceIte,
      one_mul, neg_one_mul] at hR ⊢ <;>
    field_simp [hR, exp_ne_zero] <;> ring

/-- Exact weighted square integrability under the signed logarithm.
The source set may be any measurable subset of the original core
containing the image of the selected deep tail. -/
theorem morseSecondModePullback_memLp {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {N : ℕ} {right : Bool}
    {u : ℝ → ℝ} {J : Set ℝ}
    (hreal : MorseChainRealization T σ D C) (hN : T.index < N)
    (hJ : MeasurableSet J) (hJcore : J ⊆ radialCore D)
    (himage : tailPhysicalRadius right ''
      Ioo (morseSecondModeTail D T N right).entrance
        (morseSecondModeTail D T N right).endpoint ⊆ J)
    (hu : MemLp u 2 ((radialHilbertMeasure D).restrict J))
    (hV : ContinuousOn (morseSecondModePullback D right u)
      (Ioo (morseSecondModeTail D T N right).entrance
        (morseSecondModeTail D T N right).endpoint)) :
    MemLp (morseSecondModePullback D right u) 2
      (deepTailMeasure (morseSecondModeTail D T N right)) := by
  let t := morseSecondModeTail D T N right
  let I := Ioo t.entrance t.endpoint
  let ρ : ℝ → ℝ := fun r => 12 * D.w r / r ^ 2
  have hD := morseSecondMode_profileGeometry hreal
  have hρ : ∀ r, 0 ≤ ρ r := fun r => by
    dsimp [ρ]
    exact div_nonneg (mul_nonneg (by norm_num) (radialProfileGeometry_weight_nonneg hD r))
      (sq_nonneg r)
  have hρmeas : Measurable (fun r => ENNReal.ofReal (ρ r)) :=
    ((measurable_const.mul hD.2.2.1.1.continuous.measurable).div
      (measurable_id.pow 2)).ennreal_ofReal
  have hmeasure : (radialHilbertMeasure D).restrict J =
      (volume.restrict J).withDensity (fun r => ENNReal.ofReal (ρ r)) := by
    rw [radialHilbertMeasure, restrict_withDensity hJ,
      Measure.restrict_restrict_of_subset hJcore]
  have hu₂ := hu.integrable_sq
  rw [hmeasure] at hu₂
  have hweighted := (integrable_withDensity_iff_integrable_smul'
    hρmeas (by simp)).mp hu₂
  have hweighted' : IntegrableOn (fun r => ρ r * u r ^ 2) J := by
    simpa only [ENNReal.toReal_ofReal (hρ _), smul_eq_mul] using hweighted
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := tailPhysicalRadius right)
    (f' := fun x => (if right then 1 else -1 : ℝ) * tailPhysicalRadius right x)
    (s := I) measurableSet_Ioo
    (fun x _ => (hasDerivAt_tailPhysicalRadius right x).hasDerivWithinAt)
    (tailPhysicalRadius_injective right).injOn (fun r => ρ r * u r ^ 2)
  have hpull := hchange.mp (hweighted'.mono_set himage)
  have hpull' : IntegrableOn (fun x =>
      t.p x * morseSecondModePullback D right u x ^ 2) I := by
    apply (hpull.const_mul (1 / 12 : ℝ)).congr
    filter_upwards with x
    simp only [smul_eq_mul, tailPhysicalRadius_abs_signed]
    exact (morseSecondModePullback_square_density hD T N right u x).symm
  have hpnonneg : ∀ x, 0 ≤ t.p x := by
    intro x
    change 0 ≤ morseSecondModeDensity D.w (if right then D.b else D.a)
      (if right then 1 else -1) x
    unfold morseSecondModeDensity
    exact div_nonneg
      (mul_nonneg (radialProfileGeometry_weight_nonneg hD _) (by positivity)) (by positivity)
  have hpmeas : Measurable (fun x => ENNReal.ofReal (t.p x)) :=
    (morseSecondMode_density_smooth hreal N right).continuous.measurable.ennreal_ofReal
  have hVmeas : AEStronglyMeasurable (morseSecondModePullback D right u)
      (volume.restrict I) :=
    (hV.aemeasurable measurableSet_Ioo).aestronglyMeasurable
  have hVmeas' : AEStronglyMeasurable (morseSecondModePullback D right u)
      (deepTailMeasure t) :=
    AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _) hVmeas
  apply (memLp_two_iff_integrable_sq hVmeas').mpr
  change Integrable (fun x => morseSecondModePullback D right u x ^ 2)
    ((volume.restrict I).withDensity (fun x => ENNReal.ofReal (t.p x)))
  apply (integrable_withDensity_iff_integrable_smul' hpmeas (by simp)).mpr
  simpa only [ENNReal.toReal_ofReal (hpnonneg _), smul_eq_mul] using hpull'

theorem morseSecondMode_radius_mem_naturalTail {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {N : ℕ} {right : Bool} {entry x : ℝ}
    (hreal : MorseChainRealization T σ D C) (hN : T.index < N)
    (hentry : tailPhysicalRadius right (morseSecondModeTail D T N right).entrance ∈
      radialTailInterval D right entry)
    (hx : x ∈ Ico (morseSecondModeTail D T N right).entrance
      (morseSecondModeTail D T N right).endpoint) :
    tailPhysicalRadius right x ∈ radialTailInterval D right entry := by
  have hcore := morseSecondMode_radius_mem_core hreal hN right hx
  cases right
  · change D.a < exp (-x) ∧ exp (-x) < entry
    change D.a < exp (-(morseSecondModeTail D T N false).entrance) ∧
      exp (-(morseSecondModeTail D T N false).entrance) < entry at hentry
    exact ⟨hcore.1, (exp_le_exp.mpr (neg_le_neg hx.1)).trans_lt hentry.2⟩
  · change entry < exp x ∧ exp x < D.b
    change entry < exp (morseSecondModeTail D T N true).entrance ∧
      exp (morseSecondModeTail D T N true).entrance < D.b at hentry
    exact ⟨hentry.1.trans_le (exp_le_exp.mpr hx.1), hcore.2⟩

/-- The specified radial natural solution solves the actual deep-tail
natural equation after restriction to any sufficiently deep entrance. -/
theorem morseSecondModePullback_naturalEquation {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {N : ℕ} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hN : T.index < N)
    (hphysical : TailPhysicalRelation D (morseSecondModeTail D T N right) right 2 N)
    (hentrycore : entry ∈ radialCore D)
    (hentry : tailPhysicalRadius right (morseSecondModeTail D T N right).entrance ∈
      radialTailInterval D right entry)
    (hu : RadialNaturalTail D right 2 entry u) :
    TailNaturalEquation (morseSecondModeTail D T N right)
      (morseSecondModePullback D right u) := by
  let t := morseSecondModeTail D T N right
  let V := morseSecondModePullback D right u
  have hD := morseSecondMode_profileGeometry hreal
  have hDacc : IsAccumulatingProfile D := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hacc⟩ := hreal
    exact ⟨C, hacc⟩
  have hopen : IsOpen (radialTailInterval D right entry) := by
    cases right <;> exact isOpen_Ioo
  have hJ : MeasurableSet (radialTailInterval D right entry) := hopen.measurableSet
  have hJcore : radialTailInterval D right entry ⊆ radialCore D := by
    cases right
    · intro r hr
      exact ⟨hr.1, hr.2.trans hentrycore.2⟩
    · intro r hr
      exact ⟨hentrycore.1.trans hr.1, hr.2⟩
  have hpoint (x : ℝ) (hx : x ∈ Ioo t.entrance t.endpoint) :
      ContDiffAt ℝ ∞ V x := by
    apply morseSecondModePullback_contDiffAt
    exact hu.2.1.1.contDiffAt (hopen.mem_nhds
      (morseSecondMode_radius_mem_naturalTail hreal hN hentry ⟨hx.1.le, hx.2⟩))
  have hsmooth : ContDiffOn ℝ ∞ V (Ioo t.entrance t.endpoint) :=
    fun x hx => (hpoint x hx).contDiffWithinAt
  refine ⟨morseSecondModePullback_contDiffAt (hu.2.1.1.contDiffAt
    (hopen.mem_nhds hentry)), hsmooth, ?_, ?_⟩
  · apply morseSecondModePullback_memLp hreal hN hJ hJcore _ hu.2.2.1 hsmooth.continuousOn
    rintro r ⟨x, hx, rfl⟩
    exact morseSecondMode_radius_mem_naturalTail hreal hN hentry ⟨hx.1.le, hx.2⟩
  · intro x hx
    have hr := morseSecondMode_radius_mem_naturalTail hreal hN hentry ⟨hx.1.le, hx.2⟩
    have hsource := tailPhysicalSourceIdentity_at_of_relation hDacc hphysical
      ((hpoint x hx).of_le (by simp))
      (fun y _ => morseSecondModePullback_relation hD right u y) hx
    have hzero := hsource.symm.trans (hu.2.1.2 _ hr)
    have hrad := tailPhysicalRadius_pos right x
    have hR := morseSecondMode_endpoint_pos hD right
    have hw := hD.2.2.2.2.1 _ ((hphysical.2.2.1 x hx).1)
    have hfactor : 0 <
        (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
          (((2 : ℕ) : ℝ) ^ 2) *
          D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x ^ 2 := by
      positivity
    have hz := (mul_eq_zero.mp hzero).resolve_left (neg_ne_zero.mpr hfactor.ne')
    have hp : t.p x ≠ 0 :=
      (morseSecondMode_density_pos hreal hN right ⟨hx.1.le, hx.2⟩).ne'
    field_simp [hp] at hz
    nlinarith only [hz]

end ContinuousFlexibility.Radial
