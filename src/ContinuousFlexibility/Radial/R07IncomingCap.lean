import ContinuousFlexibility.Radial.R07CapPullback

/-!
# A normalized incoming solution from a positive cap

The physical initial-value problem is solved on the entire retained
cut-to-entry interval. Riccati comparison on an oriented cap proves that
its value at the join is positive. Dividing by that value produces the
normalization and the signed derivative required in R07. The two endpoints
are handled by the same outward sign and the same cap theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

def r07OutwardSign (right : Bool) : ℝ := if right then 1 else -1

theorem r07OutwardSign_sq (right : Bool) : r07OutwardSign right ^ 2 = 1 := by
  cases right <;> norm_num [r07OutwardSign]

theorem r07OutwardSign_mul_pos_iff (right : Bool) (x : ℝ) :
    0 < r07OutwardSign right * x ↔ (if right then 0 < x else x < 0) := by
  cases right <;> simp [r07OutwardSign]

/-- Positive derivative in the outward coordinate gives the required
ordering of the physical cut and join. -/
theorem r07_cap_order (right : Bool) {R : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hR : ContDiff ℝ ∞ R)
    (hdir : ∀ x ∈ Icc 0 L, if right then 0 < deriv R x else deriv R x < 0) :
    if right then R 0 < R L else R L < R 0 := by
  have hmono : StrictMonoOn (fun x => r07OutwardSign right * R x) (Icc 0 L) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 L)
      (contDiff_const.mul hR).continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [deriv_const_mul_field]
    exact (r07OutwardSign_mul_pos_iff right _).mpr (hdir x (Ioo_subset_Icc_self hx))
  have h := hmono ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
  cases right <;> simpa [r07OutwardSign] using h

/-- The actual cap solution is positive away from its Dirichlet cut,
and the geometric Riccati bound controls its physical logarithmic slope. -/
theorem r07_cap_solution_bounds {R w u : ℝ → ℝ} {J scale L M : ℝ}
    (hL : 0 < L) (hJ : 0 < J) (hM : 0 < M) (hscale : scale ≠ 0)
    (hR : ContDiff ℝ ∞ R) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc 0 L, w (R x) = scale * deriv R x)
    (hode : ∀ x ∈ Icc 0 L, radialJacobi J w u (R x) = 0)
    (hq : ∀ x ∈ Icc 0 L,
      0 ≤ J * deriv (deriv R) x / R x ∧ J * deriv (deriv R) x / R x ≤ M ^ 2)
    (hzero : u (R 0) = 0) (hinit : 0 < deriv u (R 0) * deriv R 0)
    (hRL : 0 < R L)
    (hsmall : R L / (J * |deriv R L|) * (M + 1 / L) ≤ 1 / 2) :
    (∀ x ∈ Ioc 0 L, 0 < u (R x)) ∧
      |R L * deriv u (R L) / (J * u (R L))| ≤ 1 / 2 := by
  obtain ⟨hU, hU'⟩ := r07_cap_pullback_system hL hscale hR hw hu hweight hode
  have hpos := dirichlet_pos (M := M) hU hU' hq hzero hinit
  have hLmem : L ∈ Ioc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hval : 0 < u (R L) := (hpos L hLmem).1
  have hder : 0 < deriv u (R L) * deriv R L := (hpos L hLmem).2
  have hR' : deriv R L ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hder
    exact (lt_irrefl (0 : ℝ)) hder
  have hslope : 0 < deriv u (R L) * deriv R L / u (R L) := div_pos hder hval
  have hslope_le := dirichlet_logSlope_le_add hM hU hU' hq hzero hinit L hLmem
  have hrepr : |R L * deriv u (R L) / (J * u (R L))| =
      R L / (J * |deriv R L|) * (deriv u (R L) * deriv R L / u (R L)) := by
    calc
      _ = R L / (J * |deriv R L|) *
          |deriv u (R L) * deriv R L / u (R L)| := by
            simp only [abs_div, abs_mul, abs_of_pos hRL, abs_of_pos hJ, abs_of_pos hval]
            field_simp [hJ.ne', hval.ne', abs_ne_zero.mpr hR'] <;> ring
      _ = _ := by rw [abs_of_pos hslope]
  refine ⟨fun x hx => (hpos x hx).1, ?_⟩
  rw [hrepr]
  exact (mul_le_mul_of_nonneg_left hslope_le (by positivity)).trans hsmall

/-- A concrete positive cap and its radius-speed bound construct the
incoming solution with the exact normalization used in `IsSelectedTail`.
The solution continues through the whole physical interval `[l,h]`. -/
theorem exists_r07_normalized_incoming_cap (right : Bool) {D : Statements.ReferenceData}
    (hD : Statements.RadialProfileGeometry D) {l h L J M scale : ℝ} {R : ℝ → ℝ}
    (hl : D.a < l) (hlh : l ≤ h) (hh : h < D.b)
    (hL : 0 < L) (hJ : 0 < J) (hM : 0 < M) (hscale : scale ≠ 0)
    (hR : ContDiff ℝ ∞ R) (hmap : ∀ x ∈ Icc 0 L, R x ∈ Icc l h)
    (hdir : ∀ x ∈ Icc 0 L, if right then 0 < deriv R x else deriv R x < 0)
    (hweight : ∀ x ∈ Icc 0 L, D.w (R x) = scale * deriv R x)
    (hq : ∀ x ∈ Icc 0 L,
      0 ≤ J * deriv (deriv R) x / R x ∧ J * deriv (deriv R) x / R x ≤ M ^ 2)
    (hsmall : R L / (J * |deriv R L|) * (M + 1 / L) ≤ 1 / 2) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ u (R 0) = 0 ∧ u (R L) = 1 ∧
      (if right then 0 < deriv u (R 0) else deriv u (R 0) < 0) ∧
      (if right then R 0 < R L else R L < R 0) ∧
      (∀ r ∈ Icc l h, radialJacobi J D.w u r = 0) ∧
      (∀ x ∈ Ioc 0 L, 0 < u (R x)) ∧
      R L * deriv u (R L) / J - 1 ∈ Icc (-(3 : ℝ) / 2) (-1 / 2) := by
  have h0mem : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have hLmem : L ∈ Icc (0 : ℝ) L := ⟨hL.le, le_rfl⟩
  obtain ⟨v, hv, hv0, hv'0, hode⟩ := exists_radialSolution_on_Icc hD
    hl hlh hh (hmap 0 h0mem) J 0 (r07OutwardSign right)
  have hinit : 0 < deriv v (R 0) * deriv R 0 := by
    rw [hv'0]
    exact (r07OutwardSign_mul_pos_iff right _).mpr (hdir 0 h0mem)
  have hRL : 0 < R L := hD.1.trans (hl.trans_le (hmap L hLmem).1)
  obtain ⟨hpos, hbound⟩ := r07_cap_solution_bounds hL hJ hM hscale hR
    hD.2.2.1.1 hv hweight (fun x hx => hode (R x) (hmap x hx)) hq hv0 hinit hRL hsmall
  have hvL : 0 < v (R L) := hpos L ⟨hL, le_rfl⟩
  let u : ℝ → ℝ := fun r => (v (R L))⁻¹ * v r
  have hu : ContDiff ℝ ∞ u := contDiff_const.mul hv
  have hud (r : ℝ) : deriv u r = (v (R L))⁻¹ * deriv v r :=
    deriv_const_mul_field (v (R L))⁻¹
  have hu0 : u (R 0) = 0 := by
    change (v (R L))⁻¹ * v (R 0) = 0
    rw [hv0, mul_zero]
  have huL : u (R L) = 1 := inv_mul_cancel₀ hvL.ne'
  refine ⟨u, hu, hu0, huL, ?_, r07_cap_order right hL hR hdir, ?_, ?_, ?_⟩
  · apply (r07OutwardSign_mul_pos_iff right _).mp
    rw [hud, hv'0]
    have hsign : r07OutwardSign right * r07OutwardSign right = 1 :=
      by simpa only [pow_two] using r07OutwardSign_sq right
    have he : r07OutwardSign right * ((v (R L))⁻¹ * r07OutwardSign right) =
        (v (R L))⁻¹ := by
      calc
        _ = (v (R L))⁻¹ * (r07OutwardSign right * r07OutwardSign right) := by ring
        _ = _ := by rw [hsign, mul_one]
    rw [he]
    exact inv_pos.mpr hvL
  · intro r hr
    change radialJacobi J D.w (fun x => (v (R L))⁻¹ * v x) r = 0
    rw [radialJacobi_const_mul, hode r hr, mul_zero]
  · intro x hx
    exact mul_pos (inv_pos.mpr hvL) (hpos x hx)
  · have habs : |R L * deriv u (R L) / J| ≤ 1 / 2 := by
      calc
        _ = |R L * deriv v (R L) / (J * v (R L))| := by
          rw [hud]
          congr 1
          field_simp [hJ.ne', hvL.ne'] <;> ring
        _ ≤ _ := hbound
    exact ⟨by linarith only [(abs_le.mp habs).1],
      by linarith only [(abs_le.mp habs).2]⟩

end ContinuousFlexibility.Radial
