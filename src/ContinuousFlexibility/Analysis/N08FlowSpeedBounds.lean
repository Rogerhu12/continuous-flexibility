import ContinuousFlexibility.Analysis.N08CharacteristicVariation
import ContinuousFlexibility.Scalar.S04CalculusProof
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Parameter and angular bounds for the factored actual speed

The radial square root is continuous at a turning point and does not vary
with the height parameter or angle. The remaining factors are jointly
smooth. Compact boxes therefore provide the uniform Lipschitz domination
needed to differentiate the actual flow's integral equation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped NNReal Topology ContDiff

set_option backward.isDefEq.respectTransparency false

section Parameters

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem n08_contDiffAt_parameter_heightQ
    {W : P × ℝ → ℝ} {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hW : ContDiffAt ℝ ∞ W (p, x.1)) (hZ : ContDiffAt ℝ ∞ Z (p, x))
    (hr : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      heightQ (profileEnergy (fun r => W (s.1, r)) s.2)
        (heightRadial (fun y => Z (s.1, y)) s.2)
        (angularPartial (heightAngular (fun y => Z (s.1, y))) s.2)) (p, x) :=
  (contDiffAt_parameter_heightRadial hZ).add
    ((contDiffAt_parameter_profileEnergy (x := x) hW).mul
      (contDiffAt_parameter_angularPartial (contDiffAt_parameter_heightAngular hZ hr)))

theorem n08_contDiffAt_parameter_characteristicFactors
    {W : P × ℝ → ℝ} {Z : P × PolarPoint → ℝ} {p : P} {x : PolarPoint}
    (hW : ContDiffAt ℝ ∞ W (p, x.1)) (hZ : ContDiffAt ℝ ∞ Z (p, x))
    (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant (fun r => W (p, r)) (fun y => Z (p, y)) x)
    (hQ : 0 < heightQ (profileEnergy (fun r => W (p, r)) x)
      (heightRadial (fun y => Z (p, y)) x)
      (angularPartial (heightAngular (fun y => Z (p, y))) x)) :
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      n08CharacteristicDrift (fun r => W (s.1, r)) (fun y => Z (s.1, y)) s.2) (p, x) ∧
    ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      n08CharacteristicFactor (fun r => W (s.1, r)) (fun y => Z (s.1, y)) s.2) (p, x) := by
  have hE := contDiffAt_parameter_profileEnergy (x := x) hW
  have hp := contDiffAt_parameter_heightAngular hZ hr
  have hpr := contDiffAt_parameter_radialPartial hp
  have hq := n08_contDiffAt_parameter_heightQ hW hZ hr
  have hd := contDiffAt_parameter_polarDiscriminant hW hZ hr
  have ht : ContDiffAt ℝ ∞ (fun s : P × PolarPoint =>
      polarScale (fun r => W (s.1, r)) (fun y => Z (s.1, y)) s.2) (p, x) :=
    contDiffAt_const.div (hd.mul (hd.sqrt hD.ne'))
      (mul_ne_zero hD.ne' (Real.sqrt_pos.mpr hD).ne')
  have ha : 0 < polarLinearA (fun r => W (p, r)) (fun y => Z (p, y)) x :=
    mul_pos hQ (inverseDThreeHalves_pos _ hD)
  exact ⟨((hE.neg.mul hpr).mul ht).div (hq.mul ht) ha.ne',
    (hd.sqrt hD.ne').div hq hQ.ne'⟩

end Parameters

/-- Joint differentiability in parameter and angle holds even at a radial
turning point: its square root is constant in these two variables. -/
theorem n08_parameterAngleSpeed_differentiableAt
    {w : ℝ → ℝ} {Z : ℝ × PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hZ : ContDiff ℝ ∞ Z)
    {q r θ : ℝ} (hr : r ≠ 0)
    (hD : 0 < polarDiscriminant w (fun p => Z (q, p)) (r, θ))
    (hQ : 0 < heightQ (profileEnergy w (r, θ))
      (heightRadial (fun p => Z (q, p)) (r, θ))
      (angularPartial (heightAngular (fun p => Z (q, p))) (r, θ))) :
    DifferentiableAt ℝ
      (fun z : ℝ × ℝ => n08JacobiMinusSpeed w (fun p => Z (z.1, p)) (r, z.2)) (q, θ) := by
  have hW : ContDiff ℝ ∞ (fun s : ℝ × ℝ => w s.2) := hw.comp contDiff_snd
  have hemb : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.1, (r, z.2))) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have hf := n08_contDiffAt_parameter_characteristicFactors hW.contDiffAt
    hZ.contDiffAt hr hD hQ
  have hA := hf.1.comp (q, θ) hemb.contDiffAt
  have hB := hf.2.comp (q, θ) hemb.contDiffAt
  have hvconst : ContDiffAt ℝ ∞
      (fun _ : ℝ × ℝ => Real.sqrt (-w r * deriv w r / r)) (q, θ) := contDiffAt_const
  have hg := (hA.sub (hvconst.mul hB)).differentiableAt (by simp)
  apply hg.congr_of_eventuallyEq
  have hd := (contDiffAt_parameter_polarDiscriminant (p := q) (x := (r, θ))
    hW.contDiffAt hZ.contDiffAt hr).comp
    (q, θ) hemb.contDiffAt
  have hq := (n08_contDiffAt_parameter_heightQ (p := q) (x := (r, θ))
    hW.contDiffAt hZ.contDiffAt hr).comp
    (q, θ) hemb.contDiffAt
  have hdp : ∀ᶠ z : ℝ × ℝ in 𝓝 (q, θ),
      0 < polarDiscriminant w (fun p => Z (z.1, p)) (r, z.2) :=
    hd.continuousAt.eventually (Ioi_mem_nhds hD)
  have hqp : ∀ᶠ z : ℝ × ℝ in 𝓝 (q, θ),
      0 < heightQ (profileEnergy w (r, z.2))
        (heightRadial (fun p => Z (z.1, p)) (r, z.2))
        (angularPartial (heightAngular (fun p => Z (z.1, p))) (r, z.2)) :=
    hq.continuousAt.eventually (Ioi_mem_nhds hQ)
  filter_upwards [hdp, hqp] with z hdz hqz
  exact n08JacobiMinusSpeed_eq_factors (hw.differentiable (by simp) r) hr hdz hqz

private theorem n08_lipschitz_sub_const_mul
    {E : Type*} [PseudoMetricSpace E] {s : Set E} {f g : E → ℝ}
    {Kf Kg V : ℝ≥0} {v : ℝ}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) (hv : |v| ≤ V) :
    LipschitzOnWith (Kf + V * Kg) (fun x => f x - v * g x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have ha := hf.dist_le_mul x hx y hy
  have hb := hg.dist_le_mul x hx y hy
  rw [Real.dist_eq] at ha hb
  calc
    dist (f x - v * g x) (f y - v * g y) =
        |(f x - f y) - v * (g x - g y)| := by
      rw [Real.dist_eq]
      congr 1
      ring
    _ ≤ |f x - f y| + |v * (g x - g y)| := abs_sub _ _
    _ = |f x - f y| + |v| * |g x - g y| := by rw [abs_mul]
    _ ≤ Kf * dist x y + V * (Kg * dist x y) :=
      add_le_add ha (mul_le_mul hv hb (abs_nonneg _) (NNReal.coe_nonneg _))
    _ = (Kf + V * Kg : ℝ≥0) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      ring

/-- A compact parameter/radius/angle box gives one Lipschitz constant in
parameter and angle, uniformly in its radius, as well as joint continuity. -/
theorem n08_parameterSpeed_box
    {w : ℝ → ℝ} {Z : ℝ × PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hZ : ContDiff ℝ ∞ Z)
    {a b c d e f : ℝ} (ha : 0 < a)
    (hD : ∀ z ∈ Icc c d ×ˢ (Icc a b ×ˢ Icc e f),
      0 < polarDiscriminant w (fun p => Z (z.1, p)) z.2)
    (hQ : ∀ z ∈ Icc c d ×ˢ (Icc a b ×ˢ Icc e f),
      0 < heightQ (profileEnergy w z.2) (heightRadial (fun p => Z (z.1, p)) z.2)
        (angularPartial (heightAngular (fun p => Z (z.1, p))) z.2)) :
    ContinuousOn (fun z : ℝ × PolarPoint => n08JacobiMinusSpeed w (fun p => Z (z.1, p)) z.2)
      (Icc c d ×ˢ (Icc a b ×ˢ Icc e f)) ∧
    ∃ K : ℝ≥0, ∀ r ∈ Icc a b,
      LipschitzOnWith K
        (fun z : ℝ × ℝ => n08JacobiMinusSpeed w (fun p => Z (z.1, p)) (r, z.2))
        (Icc c d ×ˢ Icc e f) := by
  let I : Set (ℝ × PolarPoint) := Icc c d ×ˢ (Icc a b ×ˢ Icc e f)
  let A : ℝ × PolarPoint → ℝ := fun z => n08CharacteristicDrift w (fun p => Z (z.1, p)) z.2
  let B : ℝ × PolarPoint → ℝ := fun z => n08CharacteristicFactor w (fun p => Z (z.1, p)) z.2
  let v : ℝ → ℝ := fun r => Real.sqrt (-w r * deriv w r / r)
  have hW : ContDiff ℝ ∞ (fun s : ℝ × ℝ => w s.2) := hw.comp contDiff_snd
  have hreg (z : ℝ × PolarPoint) (hz : z ∈ I) :
      ContDiffAt ℝ ∞ A z ∧ ContDiffAt ℝ ∞ B z :=
    n08_contDiffAt_parameter_characteristicFactors hW.contDiffAt hZ.contDiffAt
      (ha.trans_le hz.2.1.1).ne' (hD z hz) (hQ z hz)
  have hA : ContDiffOn ℝ ∞ A I := fun z hz => (hreg z hz).1.contDiffWithinAt
  have hB : ContDiffOn ℝ ∞ B I := fun z hz => (hreg z hz).2.contDiffWithinAt
  have hconv : Convex ℝ I := (convex_Icc c d).prod ((convex_Icc a b).prod (convex_Icc e f))
  have hcompact : IsCompact I := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨KA, hKA⟩ := hA.exists_lipschitzOnWith (by simp) hconv hcompact
  obtain ⟨KB, hKB⟩ := hB.exists_lipschitzOnWith (by simp) hconv hcompact
  have hv : ContinuousOn v (Icc a b) := by
    have hwd := (contDiff_infty_iff_deriv.mp hw).2.continuous
    exact ((hw.continuous.neg.mul hwd).continuousOn.div continuous_id.continuousOn
      (fun r hr => (ha.trans_le hr.1).ne')).sqrt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  let V : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hvbound (r : ℝ) (hr : r ∈ Icc a b) : |v r| ≤ V := by
    have hn : |v r| ≤ M := by simpa only [Real.norm_eq_abs] using hM r hr
    exact hn.trans (le_max_left M 0)
  have heq (z : ℝ × PolarPoint) (hz : z ∈ I) :
      n08JacobiMinusSpeed w (fun p => Z (z.1, p)) z.2 = A z - v z.2.1 * B z :=
    n08JacobiMinusSpeed_eq_factors (hw.differentiable (by simp) z.2.1)
      (ha.trans_le hz.2.1.1).ne' (hD z hz) (hQ z hz)
  constructor
  · have hvc : ContinuousOn (fun z : ℝ × PolarPoint => v z.2.1) I :=
      hv.comp continuous_snd.fst.continuousOn (fun z hz => hz.2.1)
    exact (hA.continuousOn.sub (hvc.mul hB.continuousOn)).congr heq
  · refine ⟨KA + V * KB, ?_⟩
    intro r hr
    have hemb : LipschitzWith 1 (fun z : ℝ × ℝ => (z.1, (r, z.2))) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, NNReal.coe_one, one_mul]
      exact le_rfl
    have hmaps : MapsTo (fun z : ℝ × ℝ => (z.1, (r, z.2)))
        (Icc c d ×ˢ Icc e f) I := fun z hz => ⟨hz.1, hr, hz.2⟩
    have hAL : LipschitzOnWith KA (fun z : ℝ × ℝ => A (z.1, (r, z.2)))
        (Icc c d ×ˢ Icc e f) := by
      simpa only [mul_one, Function.comp_def] using hKA.comp hemb.lipschitzOnWith hmaps
    have hBL : LipschitzOnWith KB (fun z : ℝ × ℝ => B (z.1, (r, z.2)))
        (Icc c d ×ˢ Icc e f) := by
      simpa only [mul_one, Function.comp_def] using hKB.comp hemb.lipschitzOnWith hmaps
    have hL := n08_lipschitz_sub_const_mul hAL hBL (hvbound r hr)
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [heq _ (hmaps hx), heq _ (hmaps hy)]
    exact hL.dist_le_mul x hx y hy

end ContinuousFlexibility.Statements
