import ContinuousFlexibility.Radial.DeepTailPhysicalSource
import ContinuousFlexibility.Radial.TailMassResistanceData
import ContinuousFlexibility.Radial.OuterGreenKernel

/-!
# The actual physical lift of a natural tail solution

The inverse logarithmic coordinate and normalized gauge are evaluated on
the original radius. The resulting function has the actual derivatives
required by the radial Jacobi equation and its first-order flux system.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The logarithmic coordinate increasing towards the selected endpoint. -/
def tailPhysicalLog (right : Bool) (r : ℝ) : ℝ :=
  if right then log r else -log r

/-- The radial endpoint selected by the orientation. -/
def tailPhysicalEndpoint (D : ReferenceData) (right : Bool) : ℝ :=
  if right then D.b else D.a

/-- The normalized gauge applied to the original natural solution. -/
def tailPhysicalLift (D : ReferenceData) (right : Bool) (j : ℕ)
    (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2) * u (tailPhysicalLog right r)

theorem tailPhysicalRadius_pos (right : Bool) (x : ℝ) :
    0 < tailPhysicalRadius right x := by
  cases right <;> exact exp_pos _

theorem continuous_tailPhysicalRadius (right : Bool) : Continuous (tailPhysicalRadius right) := by
  cases right
  · exact continuous_exp.comp continuous_neg
  · exact continuous_exp

@[simp] theorem tailPhysicalLog_radius (right : Bool) (x : ℝ) :
    tailPhysicalLog right (tailPhysicalRadius right x) = x := by
  cases right <;> simp [tailPhysicalLog, tailPhysicalRadius]

theorem tailPhysicalRadius_log (right : Bool) {r : ℝ} (hr : 0 < r) :
    tailPhysicalRadius right (tailPhysicalLog right r) = r := by
  cases right <;> simp [tailPhysicalLog, tailPhysicalRadius, exp_log hr]

@[simp] theorem tailPhysicalLift_radius (D : ReferenceData) (right : Bool)
    (j : ℕ) (u : ℝ → ℝ) (x : ℝ) :
    tailPhysicalLift D right j u (tailPhysicalRadius right x) =
      (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2) * u x := by
  simp [tailPhysicalLift]

theorem tailPhysicalEndpoint_pos {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (right : Bool) : 0 < tailPhysicalEndpoint D right := by
  obtain ⟨C, hC⟩ := hD
  cases right
  · exact hC.1.1
  · exact hC.1.1.trans hC.1.2.1

theorem contDiffAt_tailPhysicalLog (right : Bool) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (tailPhysicalLog right) r := by
  cases right
  · exact (contDiffAt_log.mpr hr).neg
  · exact contDiffAt_log.mpr hr

theorem contDiffAt_tailPhysicalLift {D : ReferenceData} {right : Bool} {j : ℕ}
    {u : ℝ → ℝ} {r : ℝ} (hR : tailPhysicalEndpoint D right ≠ 0) (hr : 0 < r)
    (hu : ContDiffAt ℝ ∞ u (tailPhysicalLog right r)) :
    ContDiffAt ℝ ∞ (tailPhysicalLift D right j u) r := by
  exact ((contDiffAt_id.div_const _).rpow_const_of_ne (div_ne_zero hr.ne' hR)).mul
    (hu.comp r (contDiffAt_tailPhysicalLog right hr.ne'))

theorem tailNatural_contDiffAt {T : DeepTailData} {u : ℝ → ℝ}
    (hu : TailNaturalEquation T u) {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    ContDiffAt ℝ ∞ u x :=
  hu.2.1.contDiffAt (isOpen_Ioo.mem_nhds hx)

theorem tailNaturalLift_contDiffAt {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hu : TailNaturalEquation T u) {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    ContDiffAt ℝ ∞ (tailPhysicalLift D right j u) (tailPhysicalRadius right x) := by
  apply contDiffAt_tailPhysicalLift (tailPhysicalEndpoint_pos hD right).ne'
    (tailPhysicalRadius_pos right x)
  simpa only [tailPhysicalLog_radius] using tailNatural_contDiffAt hu hx

/-- The lift solves the exact radial Jacobi equation in the original
radius; the logarithmic source vanishes by the natural divergence equation. -/
theorem tailNaturalLift_radialJacobi {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hu : TailNaturalEquation T u) {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j u)
      (tailPhysicalRadius right x) = 0 := by
  rw [tailPhysicalSourceIdentity_at_of_relation hD hphysical
    ((tailNatural_contDiffAt hu hx).of_le (by simp))
    (fun y _ => tailPhysicalLift_radius D right j u y) hx]
  have hp : T.p x ≠ 0 := (deepTail_pos hT x ⟨hx.1.le, hx.2⟩).ne'
  have heq : deriv (fun y => T.p y * deriv u y) x = -T.Λ * T.p x * u x := by
    linarith [hu.2.2.2 x hx]
  have hzero : -(T.p x)⁻¹ * deriv (fun y => T.p y * deriv u y) x - T.Λ * u x = 0 := by
    rw [heq]
    field_simp [hp] <;> ring
  rw [hzero, mul_zero]

/-- The physical flux associated with the lifted natural solution. -/
def tailPhysicalFlux (D : ReferenceData) (right : Bool) (j : ℕ)
    (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  D.w r * deriv (tailPhysicalLift D right j u) r

theorem tailNaturalFlux_contDiffAt {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hu : TailNaturalEquation T u) {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    ContDiffAt ℝ ∞ (tailPhysicalFlux D right j u) (tailPhysicalRadius right x) := by
  obtain ⟨C, hC⟩ := hD
  exact hC.1.2.2.1.1.contDiffAt.mul
    ((tailNaturalLift_contDiffAt ⟨C, hC⟩ hu hx).derivWithin (by simp))

theorem tailNaturalLift_contDiffAt_entrance {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hu : TailNaturalEquation T u) :
    ContDiffAt ℝ ∞ (tailPhysicalLift D right j u) (tailPhysicalRadius right T.entrance) := by
  apply contDiffAt_tailPhysicalLift (tailPhysicalEndpoint_pos hD right).ne'
    (tailPhysicalRadius_pos right T.entrance)
  simpa only [tailPhysicalLog_radius] using hu.1

theorem tailNaturalFlux_contDiffAt_entrance {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hu : TailNaturalEquation T u) :
    ContDiffAt ℝ ∞ (tailPhysicalFlux D right j u) (tailPhysicalRadius right T.entrance) := by
  obtain ⟨C, hC⟩ := hD
  exact hC.1.2.2.1.1.contDiffAt.mul
    ((tailNaturalLift_contDiffAt_entrance ⟨C, hC⟩ hu).derivWithin (by simp))

/-- The two actual first-order equations used for propagation of all
physical derivative estimates. -/
theorem tailNaturalLift_firstOrder {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hu : TailNaturalEquation T u) {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    deriv (tailPhysicalLift D right j u) (tailPhysicalRadius right x) =
        (D.w (tailPhysicalRadius right x))⁻¹ *
          tailPhysicalFlux D right j u (tailPhysicalRadius right x) ∧
      deriv (tailPhysicalFlux D right j u) (tailPhysicalRadius right x) =
        ((j : ℝ) ^ 2 * (deriv D.w (tailPhysicalRadius right x) *
          (tailPhysicalRadius right x)⁻¹)) *
            tailPhysicalLift D right j u (tailPhysicalRadius right x) := by
  obtain ⟨C, hC⟩ := hD
  have hcore := (hphysical.2.2.1 x hx).1
  have hw₀ : D.w (tailPhysicalRadius right x) ≠ 0 :=
    (hC.1.2.2.2.2.1 _ hcore).ne'
  have hw := hC.1.2.2.1.1.differentiable (by simp) (tailPhysicalRadius right x)
  have hv := tailNaturalLift_contDiffAt (right := right) (j := j) ⟨C, hC⟩ hu hx
  constructor
  · simp only [tailPhysicalFlux, ← mul_assoc, inv_mul_cancel₀ hw₀, one_mul]
  · have hd := hasDerivAt_flux_of_radialJacobi_eq_zero hw
      ((hv.derivWithin (m := ∞) (by simp)).differentiableAt (by simp))
      (tailNaturalLift_radialJacobi ⟨C, hC⟩ hT hphysical hu hx)
    simpa only [tailPhysicalFlux, div_eq_mul_inv, mul_assoc] using hd.deriv

/-- The derivative of the normalized gauge, with the orientation sign
kept explicit in the logarithmic derivative. -/
theorem hasDerivAt_tailPhysicalLift {D : ReferenceData} {right : Bool} {j : ℕ}
    {u : ℝ → ℝ} {r : ℝ} (hR : 0 < tailPhysicalEndpoint D right) (hr : 0 < r)
    (hu : DifferentiableAt ℝ u (tailPhysicalLog right r)) :
    HasDerivAt (tailPhysicalLift D right j u)
      ((r / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2) / r *
        ((j : ℝ) ^ 2 * u (tailPhysicalLog right r) +
          (if right then 1 else -1 : ℝ) * deriv u (tailPhysicalLog right r))) r := by
  have hratio : 0 < r / tailPhysicalEndpoint D right := div_pos hr hR
  have hc : HasDerivAt (tailPhysicalLog right)
      ((if right then 1 else -1 : ℝ) / r) r := by
    cases right
    · change HasDerivAt (fun y : ℝ => -log y) ((-1 : ℝ) / r) r
      convert (hasDerivAt_neg (log r)).comp r (hasDerivAt_log hr.ne') using 1 <;>
        simp [Function.comp_def, div_eq_mul_inv]
    · change HasDerivAt log ((1 : ℝ) / r) r
      simpa only [one_div] using hasDerivAt_log hr.ne'
  have hg := ((hasDerivAt_id r).div_const (tailPhysicalEndpoint D right)).rpow_const
    (p := (j : ℝ) ^ 2) (Or.inl hratio.ne')
  apply (hg.mul (hu.hasDerivAt.comp r hc)).congr_deriv
  try simp only [rpow_sub hratio, rpow_one]
  field_simp [hr.ne', hR.ne'] <;> ring

/-- In the flux formula the singular factor from differentiating the
natural solution cancels against the physical density. All remaining
gauge factors are bounded on the fixed positive radial interval. -/
theorem tailPhysicalFlux_radius {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {u : ℝ → ℝ} (hD : IsAccumulatingProfile D)
    (hphysical : TailPhysicalRelation D T right j start)
    (hu : TailNaturalEquation T u) {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    tailPhysicalFlux D right j u (tailPhysicalRadius right x) =
      ((j : ℝ) ^ 2 *
        ((tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2) *
          D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x)) * u x +
      (if right then 1 else -1 : ℝ) *
        ((tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2))⁻¹ *
          (T.p x * deriv u x) := by
  have hr := tailPhysicalRadius_pos right x
  have hR := tailPhysicalEndpoint_pos hD right
  have hratio : 0 < tailPhysicalRadius right x / tailPhysicalEndpoint D right := div_pos hr hR
  have hu' : DifferentiableAt ℝ u (tailPhysicalLog right (tailPhysicalRadius right x)) := by
    simpa only [tailPhysicalLog_radius] using (tailNatural_contDiffAt hu hx).differentiableAt
      (by simp)
  have hd := (hasDerivAt_tailPhysicalLift hR hr hu').deriv
  simp only [tailPhysicalLog_radius] at hd
  have hp : T.p x =
      ((tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2 *
        D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x := by
    rw [(hphysical.2.2.1 x hx).2]
    have hpow : (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^
        (2 * (j : ℝ) ^ 2) =
        ((tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2 := by
      rw [mul_comm (2 : ℝ), rpow_mul hratio.le]
      simp
    exact congrArg (fun y => y * D.w (tailPhysicalRadius right x) /
      tailPhysicalRadius right x) hpow
  unfold tailPhysicalFlux
  rw [hd, hp]
  field_simp [hr.ne', (rpow_pos_of_pos hratio ((j : ℝ) ^ 2)).ne'] <;> ring

/-- Continuity forces the physical density formula to hold at the regular
entrance as well, although the relation is stated only on the open tail. -/
theorem tailPhysical_density_at_entrance {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start) :
    T.p T.entrance =
      (tailPhysicalRadius right T.entrance / tailPhysicalEndpoint D right) ^
        (2 * (j : ℝ) ^ 2) * D.w (tailPhysicalRadius right T.entrance) /
          tailPhysicalRadius right T.entrance := by
  let P : ℝ → ℝ := fun x =>
    (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (2 * (j : ℝ) ^ 2) *
      D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x
  have hp : Tendsto T.p (𝓝[>] T.entrance) (𝓝 (T.p T.entrance)) := by
    have hh := ((deepTail_contDiffOn hT).continuousOn T.entrance
      ⟨le_rfl, hT.1⟩).mono Ioo_subset_Ico_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hT.1] using hh
  have hR := tailPhysicalEndpoint_pos hD right
  have hr := tailPhysicalRadius_pos right T.entrance
  obtain ⟨C, hC⟩ := hD
  have hc := (continuous_tailPhysicalRadius right).continuousAt (x := T.entrance)
  have hP : ContinuousAt P T.entrance :=
    (((hc.div_const _).rpow_const (Or.inl (div_pos hr hR).ne')).mul
      (hC.1.2.2.1.1.continuous.continuousAt.comp hc)).div hc hr.ne'
  have heq : P =ᶠ[𝓝[>] T.entrance] T.p :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hT.1) (fun x hx => (hphysical.2.2.1 x hx).2.symm)
  exact tendsto_nhds_unique hp (hP.tendsto.mono_left nhdsWithin_le_nhds |>.congr' heq)

/-- The entrance lies strictly inside the physical annulus. Otherwise
endpoint flatness would make the positive entrance density vanish. -/
theorem tailPhysical_entrance_mem_core {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start) :
    tailPhysicalRadius right T.entrance ∈ radialCore D := by
  have hp := deepTail_pos hT T.entrance ⟨le_rfl, hT.1⟩
  have heq := tailPhysical_density_at_entrance hD hT hphysical
  have hw : D.w (tailPhysicalRadius right T.entrance) ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_div] at heq
    exact hp.ne' heq
  obtain ⟨C, hC⟩ := hD
  constructor
  · by_contra h
    exact hw (hC.1.2.2.1.2 _ (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hw (hC.1.2.2.1.2 _ (Or.inr (le_of_not_gt h)))

end ContinuousFlexibility.Radial
