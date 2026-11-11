import ContinuousFlexibility.Radial.DirichletRiccatiComparison
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp

/-!
# The positive normalized slope of an incoming stand-in

The radial spectral parameter is `J = j^2`. With outward sign `ε`, the
physical impedance is `ε W u' / u` and the boundary scale is `J W / r`.
Their quotient does not depend on the profile height `W`.

On a positive cap, Riccati comparison supplies both strict positivity and
the upper bound from a geometric smallness condition. The input is the
actual scalar system for the pulled-back physical solution, so the result
can be applied directly to an oriented radius parametrization. The same
proof covers both signs of the physical radius derivative.

The first band uses the growing cone solution. Its normalized slope is
exactly `1 / j`; a finite Dirichlet cone is a different solution and would
not give the required upper bound at `j = 2`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real

/-- The physical normalization used at a truncation boundary. -/
def standInBoundaryScale (J W r : ℝ) : ℝ := J * W / r

/-- The impedance divided by the physical boundary scale, with the
positive profile height already canceled. -/
def standInBoundarySlope (ε J r : ℝ) (u : ℝ → ℝ) : ℝ :=
  ε * r * deriv u r / (J * u r)

theorem standInBoundaryScale_pos {J W r : ℝ}
    (hJ : 0 < J) (hW : 0 < W) (hr : 0 < r) :
    0 < standInBoundaryScale J W r :=
  div_pos (mul_pos hJ hW) hr

/-- The scalar defined above is the quotient of the actual outward
impedance and the actual matching scale. -/
theorem standInBoundarySlope_eq_impedance {ε J W r : ℝ} {u : ℝ → ℝ}
    (hJ : J ≠ 0) (hW : W ≠ 0) (hr : r ≠ 0) (hu : u r ≠ 0) :
    standInBoundarySlope ε J r u =
      (ε * W * deriv u r / u r) / standInBoundaryScale J W r := by
  unfold standInBoundarySlope standInBoundaryScale
  field_simp [hJ, hW, hr, hu] <;> ring

/-- Express the signed physical logarithmic slope in the outward model
coordinate. Positivity of `ε R'` is the sole orientation condition. -/
theorem standInBoundarySlope_eq_capSlope {ε J L : ℝ} {R u : ℝ → ℝ}
    (hε : ε = 1 ∨ ε = -1) (hJ : J ≠ 0) (hu : u (R L) ≠ 0)
    (hdir : 0 < ε * deriv R L) :
    standInBoundarySlope ε J (R L) u =
      R L / (J * |deriv R L|) * (deriv u (R L) * deriv R L / u (R L)) := by
  unfold standInBoundarySlope
  rcases hε with rfl | rfl
  · have hspeed : 0 < deriv R L := by simpa only [one_mul] using hdir
    rw [abs_of_pos hspeed]
    field_simp [hJ, hu, hspeed.ne'] <;> ring
  · have hspeed : deriv R L < 0 := by nlinarith only [hdir]
    rw [abs_of_neg hspeed]
    field_simp [hJ, hu, ne_of_lt hspeed] <;> ring

/-- A convenient purely geometric way to check the Riccati smallness
condition: allocate one quarter to each term in `M + 1/L`. -/
theorem standIn_cap_geometry_small {r J speed M L : ℝ}
    (hpotential : r / (J * |speed|) * M ≤ 1 / 4)
    (hlength : r / (J * |speed|) / L ≤ 1 / 4) :
    r / (J * |speed|) * (M + 1 / L) ≤ 1 / 2 := by
  calc
    _ = r / (J * |speed|) * M + r / (J * |speed|) / L := by ring
    _ ≤ 1 / 4 + 1 / 4 := add_le_add hpotential hlength
    _ = _ := by norm_num

/-- Riccati comparison proves the actual stand-in bound. The smallness
hypothesis contains only the cap geometry and the potential bound, not the
unknown solution or its final logarithmic slope. The scalar system can be
provided by the physical radial equation under any oriented cap pullback. -/
theorem standInBoundarySlope_bounds_of_cap
    {ε J L M : ℝ} {R u q : ℝ → ℝ}
    (hε : ε = 1 ∨ ε = -1) (hL : 0 < L) (hJ : 0 < J) (hM : 0 < M)
    (hr : 0 < R L) (hdir : 0 < ε * deriv R L)
    (hU : ∀ x ∈ Icc 0 L,
      HasDerivAt (fun t => u (R t)) (deriv u (R x) * deriv R x) x)
    (hU' : ∀ x ∈ Icc 0 L,
      HasDerivAt (fun t => deriv u (R t) * deriv R t) (q x * u (R x)) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2)
    (hzero : u (R 0) = 0) (hinit : 0 < deriv u (R 0) * deriv R 0)
    (hsmall : R L / (J * |deriv R L|) * (M + 1 / L) ≤ 1 / 2) :
    0 < u (R L) ∧ 0 < standInBoundarySlope ε J (R L) u ∧
      standInBoundarySlope ε J (R L) u ≤ 1 / 2 := by
  have hLmem : L ∈ Ioc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hvalue : 0 < u (R L) := (dirichlet_pos hU hU' hq hzero hinit L hLmem).1
  have hlogpos := dirichlet_logSlope_pos hU hU' hq hzero hinit L hLmem
  have hlogle := dirichlet_logSlope_le_add hM hU hU' hq hzero hinit L hLmem
  have hspeed : deriv R L ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdir
    exact (lt_irrefl (0 : ℝ)) hdir
  have hfactor : 0 < R L / (J * |deriv R L|) :=
    div_pos hr (mul_pos hJ (abs_pos.mpr hspeed))
  have heq := standInBoundarySlope_eq_capSlope hε hJ.ne' hvalue.ne' hdir
  refine ⟨hvalue, ?_, ?_⟩
  · rw [heq]
    exact mul_pos hfactor hlogpos
  · rw [heq]
    exact (mul_le_mul_of_nonneg_left hlogle hfactor.le).trans hsmall

/-- The matching coordinates of a normalized cap solution are `(1,d)`.
This records the outward physical flux, not an unsigned surrogate. -/
theorem standInBoundarySlope_normalized_flux {ε J W r : ℝ} {u : ℝ → ℝ}
    (hJ : J ≠ 0) (hW : W ≠ 0) (hr : r ≠ 0) (hu : u r = 1) :
    (u r, ε * W * deriv u r / standInBoundaryScale J W r) =
      (1, standInBoundarySlope ε J r u) := by
  apply Prod.ext
  · exact hu
  · dsimp only
    rw [standInBoundarySlope_eq_impedance hJ hW hr (by rw [hu]; exact one_ne_zero), hu]
    simp only [div_one]

/-- On a growing cone, the physical derivative relation determines the
normalized slope exactly. It is valid for either endpoint orientation. -/
theorem standInBoundarySlope_of_cone_derivative {ε j r : ℝ} {u : ℝ → ℝ}
    (hε : ε = 1 ∨ ε = -1) (hj : j ≠ 0) (hr : r ≠ 0) (hu : u r ≠ 0)
    (hder : deriv u r = ε * j * u r / r) :
    standInBoundarySlope ε (j ^ 2) r u = 1 / j := by
  unfold standInBoundarySlope
  rw [hder]
  rcases hε with rfl | rfl <;> field_simp [hj, hr, hu] <;> ring

/-- The actual positive growing solution on a cone, normalized at `c`. -/
def standInConeSolution (ε j c : ℝ) (r : ℝ) : ℝ :=
  exp (ε * j * (log r - log c))

theorem standInConeSolution_pos (ε j c r : ℝ) : 0 < standInConeSolution ε j c r :=
  exp_pos _

theorem standInConeSolution_base (ε j c : ℝ) : standInConeSolution ε j c c = 1 := by
  simp [standInConeSolution]

theorem hasDerivAt_standInConeSolution (ε j c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (standInConeSolution ε j c) (ε * j * standInConeSolution ε j c r / r) r := by
  have hlog := (hasDerivAt_log hr.ne').sub_const (log c)
  have he := (hlog.const_mul (ε * j)).exp
  convert he using 1 <;> simp only [standInConeSolution, div_eq_mul_inv] <;> ring

/-- The first-band artificial impedance has `d = 1/j` at every positive
radius of the cone, independently of the cone's length. -/
theorem standInBoundarySlope_cone_eq {ε j c r : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hj : j ≠ 0) (hr : 0 < r) :
    standInBoundarySlope ε (j ^ 2) r (standInConeSolution ε j c) = 1 / j :=
  standInBoundarySlope_of_cone_derivative hε hj hr.ne'
    (standInConeSolution_pos ε j c r).ne' (hasDerivAt_standInConeSolution ε j c hr).deriv

theorem standInBoundarySlope_cone_bounds {ε j c r : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hj : 2 ≤ j) (hr : 0 < r) :
    0 < standInBoundarySlope ε (j ^ 2) r (standInConeSolution ε j c) ∧
      standInBoundarySlope ε (j ^ 2) r (standInConeSolution ε j c) ≤ 1 / 2 := by
  have hjpos : 0 < j := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hj
  rw [standInBoundarySlope_cone_eq hε hjpos.ne' hr]
  refine ⟨div_pos zero_lt_one hjpos, ?_⟩
  apply (div_le_div_iff₀ hjpos (by norm_num : (0 : ℝ) < 2)).mpr
  simpa only [one_mul] using hj

end ContinuousFlexibility.Radial
