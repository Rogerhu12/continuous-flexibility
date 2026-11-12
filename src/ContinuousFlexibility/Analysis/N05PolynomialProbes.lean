import ContinuousFlexibility.Analysis.N05ReferenceSymbols

/-!
# Actual polynomial probes for coefficient identification

All identities use the real Frechet partial derivatives of the displayed
polynomials.  The first flux formulas impose no regularity on the coefficient
fields; this permits differentiation itself to be recovered from operator data.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n05RadialLinear (x y : PolarPoint) : ℝ := y.1 - x.1
def n05AngularLinear (x y : PolarPoint) : ℝ := y.2 - x.2

theorem n05RadialLinear_contDiff (x : PolarPoint) :
    ContDiff ℝ ∞ (n05RadialLinear x) := contDiff_fst.sub contDiff_const

theorem n05AngularLinear_contDiff (x : PolarPoint) :
    ContDiff ℝ ∞ (n05AngularLinear x) := contDiff_snd.sub contDiff_const

@[simp] theorem n05RadialLinear_self (x : PolarPoint) : n05RadialLinear x x = 0 := sub_self _
@[simp] theorem n05AngularLinear_self (x : PolarPoint) : n05AngularLinear x x = 0 := sub_self _

@[simp] theorem n05RadialLinear_radial (x : PolarPoint) :
    radialPartial (n05RadialLinear x) = fun _ => 1 := by
  funext y
  change radialPartial (fun z : PolarPoint => z.1 - x.1) y = 1
  simpa only [radialPartial_fst, radialPartial_const, sub_zero] using
    (radialPartial_sub (x := y) differentiableAt_fst (differentiableAt_const x.1))

@[simp] theorem n05RadialLinear_angular (x : PolarPoint) :
    angularPartial (n05RadialLinear x) = fun _ => 0 := by
  funext y
  change angularPartial (fun z : PolarPoint => z.1 - x.1) y = 0
  simpa only [angularPartial_fst, angularPartial_const, sub_zero] using
    (angularPartial_sub (x := y) differentiableAt_fst (differentiableAt_const x.1))

@[simp] theorem n05AngularLinear_radial (x : PolarPoint) :
    radialPartial (n05AngularLinear x) = fun _ => 0 := by
  funext y
  change radialPartial (fun z : PolarPoint => z.2 - x.2) y = 0
  simpa only [radialPartial_snd, radialPartial_const, sub_zero] using
    (radialPartial_sub (x := y) differentiableAt_snd (differentiableAt_const x.2))

@[simp] theorem n05AngularLinear_angular (x : PolarPoint) :
    angularPartial (n05AngularLinear x) = fun _ => 1 := by
  funext y
  change angularPartial (fun z : PolarPoint => z.2 - x.2) y = 1
  simpa only [angularPartial_snd, angularPartial_const, sub_zero] using
    (angularPartial_sub (x := y) differentiableAt_snd (differentiableAt_const x.2))

def n05RadialProbe (x : PolarPoint) (s : ℝ) (y : PolarPoint) : ℝ :=
  n05AngularLinear x y + s * n05RadialLinear x y ^ 2

def n05AngularProbe (x : PolarPoint) (s : ℝ) (y : PolarPoint) : ℝ :=
  n05AngularLinear x y + s * n05AngularLinear x y ^ 2

def n05MixedProbe (x y : PolarPoint) : ℝ :=
  n05RadialLinear x y * n05AngularLinear x y

theorem n05RadialProbe_contDiff (x : PolarPoint) (s : ℝ) :
    ContDiff ℝ ∞ (n05RadialProbe x s) :=
  (n05AngularLinear_contDiff x).add
    (contDiff_const.mul ((n05RadialLinear_contDiff x).pow 2))

theorem n05AngularProbe_contDiff (x : PolarPoint) (s : ℝ) :
    ContDiff ℝ ∞ (n05AngularProbe x s) :=
  (n05AngularLinear_contDiff x).add
    (contDiff_const.mul ((n05AngularLinear_contDiff x).pow 2))

theorem n05MixedProbe_contDiff (x : PolarPoint) :
    ContDiff ℝ ∞ (n05MixedProbe x) :=
  (n05RadialLinear_contDiff x).mul (n05AngularLinear_contDiff x)

theorem n05RadialProbe_partials (x : PolarPoint) (s : ℝ) :
    radialPartial (n05RadialProbe x s) = (fun y => 2 * s * n05RadialLinear x y) ∧
      angularPartial (n05RadialProbe x s) = (fun _ => 1) := by
  constructor <;> funext y
  · have hr := (n05RadialLinear_contDiff x).differentiable (by simp) y
    have ht := (n05AngularLinear_contDiff x).differentiable (by simp) y
    have hr2 : DifferentiableAt ℝ (fun q => n05RadialLinear x q ^ 2) y := hr.pow 2
    have hs : DifferentiableAt ℝ (fun q => s * n05RadialLinear x q ^ 2) y :=
      (differentiableAt_const s).mul hr2
    unfold n05RadialProbe
    rw [radialPartial_add ht hs,
      radialPartial_mul (differentiableAt_const s) hr2, radialPartial_sq hr]
    simp only [n05RadialLinear_radial, n05AngularLinear_radial, radialPartial_const]
    ring
  · have hr := (n05RadialLinear_contDiff x).differentiable (by simp) y
    have ht := (n05AngularLinear_contDiff x).differentiable (by simp) y
    have hr2 : DifferentiableAt ℝ (fun q => n05RadialLinear x q ^ 2) y := hr.pow 2
    have hs : DifferentiableAt ℝ (fun q => s * n05RadialLinear x q ^ 2) y :=
      (differentiableAt_const s).mul hr2
    unfold n05RadialProbe
    rw [angularPartial_add ht hs,
      angularPartial_mul (differentiableAt_const s) hr2, angularPartial_sq hr]
    simp only [n05RadialLinear_angular, n05AngularLinear_angular, angularPartial_const]
    ring

theorem n05AngularProbe_partials (x : PolarPoint) (s : ℝ) :
    radialPartial (n05AngularProbe x s) = (fun _ => 0) ∧
      angularPartial (n05AngularProbe x s) =
        (fun y => 1 + 2 * s * n05AngularLinear x y) := by
  constructor <;> funext y
  · have ht := (n05AngularLinear_contDiff x).differentiable (by simp) y
    have ht2 : DifferentiableAt ℝ (fun q => n05AngularLinear x q ^ 2) y := ht.pow 2
    have hs : DifferentiableAt ℝ (fun q => s * n05AngularLinear x q ^ 2) y :=
      (differentiableAt_const s).mul ht2
    unfold n05AngularProbe
    rw [radialPartial_add ht hs,
      radialPartial_mul (differentiableAt_const s) ht2, radialPartial_sq ht]
    simp only [n05AngularLinear_radial, radialPartial_const]
    ring
  · have ht := (n05AngularLinear_contDiff x).differentiable (by simp) y
    have ht2 : DifferentiableAt ℝ (fun q => n05AngularLinear x q ^ 2) y := ht.pow 2
    have hs : DifferentiableAt ℝ (fun q => s * n05AngularLinear x q ^ 2) y :=
      (differentiableAt_const s).mul ht2
    unfold n05AngularProbe
    rw [angularPartial_add ht hs,
      angularPartial_mul (differentiableAt_const s) ht2, angularPartial_sq ht]
    simp only [n05AngularLinear_angular, angularPartial_const]
    ring

theorem n05MixedProbe_partials (x : PolarPoint) :
    radialPartial (n05MixedProbe x) = n05AngularLinear x ∧
      angularPartial (n05MixedProbe x) = n05RadialLinear x := by
  constructor <;> funext y
  · unfold n05MixedProbe
    rw [radialPartial_mul
      ((n05RadialLinear_contDiff x).differentiable (by simp) y)
      ((n05AngularLinear_contDiff x).differentiable (by simp) y)]
    simp only [n05RadialLinear_radial, n05AngularLinear_radial, one_mul, mul_zero, add_zero]
  · unfold n05MixedProbe
    rw [angularPartial_mul
      ((n05RadialLinear_contDiff x).differentiable (by simp) y)
      ((n05AngularLinear_contDiff x).differentiable (by simp) y)]
    simp only [n05RadialLinear_angular, n05AngularLinear_angular, zero_mul, mul_one, zero_add]

theorem n05_divergence_radialProbe_flux (L : SymmetricCoefficients) (x : PolarPoint) (s : ℝ) :
    divergenceOperator L (n05RadialProbe x s) x =
      radialPartial (fun y => 2 * s * L.a y * n05RadialLinear x y + L.b y) x +
        angularPartial (fun y => 2 * s * L.b y * n05RadialLinear x y + L.c y) x := by
  unfold divergenceOperator
  rw [(n05RadialProbe_partials x s).1, (n05RadialProbe_partials x s).2]
  congr 1
  · apply congrArg (fun F : PolarPoint → ℝ => radialPartial F x)
    funext y
    ring
  · apply congrArg (fun F : PolarPoint → ℝ => angularPartial F x)
    funext y
    ring

theorem n05_divergence_angularProbe_flux (L : SymmetricCoefficients) (x : PolarPoint) (s : ℝ) :
    divergenceOperator L (n05AngularProbe x s) x =
      radialPartial (fun y => L.b y * (1 + 2 * s * n05AngularLinear x y)) x +
        angularPartial (fun y => L.c y * (1 + 2 * s * n05AngularLinear x y)) x := by
  unfold divergenceOperator
  rw [(n05AngularProbe_partials x s).1, (n05AngularProbe_partials x s).2]
  simp only [mul_zero, zero_add]

theorem n05_divergence_radialProbe {L : SymmetricCoefficients} {x : PolarPoint}
    (ha : DifferentiableAt ℝ L.a x) (hb : DifferentiableAt ℝ L.b x)
    (hc : DifferentiableAt ℝ L.c x) (s : ℝ) :
    divergenceOperator L (n05RadialProbe x s) x =
      2 * s * L.a x + radialPartial L.b x + angularPartial L.c x := by
  rw [n05_divergence_radialProbe_flux]
  have hr := (n05RadialLinear_contDiff x).differentiable (by simp) x
  have hsa : DifferentiableAt ℝ (fun y => 2 * s * L.a y) x :=
    (differentiableAt_const (2 * s)).mul ha
  have hsb : DifferentiableAt ℝ (fun y => 2 * s * L.b y) x :=
    (differentiableAt_const (2 * s)).mul hb
  have hsaR : DifferentiableAt ℝ (fun y => 2 * s * L.a y * n05RadialLinear x y) x :=
    hsa.mul hr
  have hsbR : DifferentiableAt ℝ (fun y => 2 * s * L.b y * n05RadialLinear x y) x :=
    hsb.mul hr
  rw [radialPartial_add hsaR hb, angularPartial_add hsbR hc,
    radialPartial_mul hsa hr, angularPartial_mul hsb hr]
  simp only [n05RadialLinear_self, n05RadialLinear_radial, n05RadialLinear_angular,
    mul_zero, zero_add, mul_one, add_zero]

theorem n05_divergence_angularProbe {L : SymmetricCoefficients} {x : PolarPoint}
    (hb : DifferentiableAt ℝ L.b x) (hc : DifferentiableAt ℝ L.c x) (s : ℝ) :
    divergenceOperator L (n05AngularProbe x s) x =
      radialPartial L.b x + angularPartial L.c x + 2 * s * L.c x := by
  rw [n05_divergence_angularProbe_flux]
  have ht := (n05AngularLinear_contDiff x).differentiable (by simp) x
  have hscaled : DifferentiableAt ℝ (fun y => 2 * s * n05AngularLinear x y) x :=
    (differentiableAt_const (2 * s)).mul ht
  have hs : DifferentiableAt ℝ (fun y => 1 + 2 * s * n05AngularLinear x y) x :=
    (differentiableAt_const (1 : ℝ)).add hscaled
  rw [radialPartial_mul hb hs, angularPartial_mul hc hs,
    radialPartial_add (differentiableAt_const (1 : ℝ)) hscaled,
    angularPartial_add (differentiableAt_const (1 : ℝ)) hscaled,
    radialPartial_mul (differentiableAt_const (2 * s)) ht,
    angularPartial_mul (differentiableAt_const (2 * s)) ht]
  simp only [n05AngularLinear_self, n05AngularLinear_radial, n05AngularLinear_angular,
    radialPartial_const, angularPartial_const, mul_zero, zero_mul, add_zero, zero_add, mul_one]
  ring

theorem n05_divergence_mixedProbe {L : SymmetricCoefficients} {x : PolarPoint}
    (ha : DifferentiableAt ℝ L.a x) (hb : DifferentiableAt ℝ L.b x)
    (hc : DifferentiableAt ℝ L.c x) :
    divergenceOperator L (n05MixedProbe x) x = 2 * L.b x := by
  unfold divergenceOperator
  rw [(n05MixedProbe_partials x).1, (n05MixedProbe_partials x).2]
  have hr := (n05RadialLinear_contDiff x).differentiable (by simp) x
  have ht := (n05AngularLinear_contDiff x).differentiable (by simp) x
  have hNa : DifferentiableAt ℝ (fun y => L.a y * n05AngularLinear x y) x := ha.mul ht
  have hNb : DifferentiableAt ℝ (fun y => L.b y * n05RadialLinear x y) x := hb.mul hr
  have hTb : DifferentiableAt ℝ (fun y => L.b y * n05AngularLinear x y) x := hb.mul ht
  have hTc : DifferentiableAt ℝ (fun y => L.c y * n05RadialLinear x y) x := hc.mul hr
  rw [radialPartial_add hNa hNb,
    angularPartial_add hTb hTc,
    radialPartial_mul ha ht, radialPartial_mul hb hr,
    angularPartial_mul hb ht, angularPartial_mul hc hr]
  simp only [n05RadialLinear_self, n05AngularLinear_self,
    n05RadialLinear_radial, n05RadialLinear_angular,
    n05AngularLinear_radial, n05AngularLinear_angular,
    mul_zero, zero_mul, mul_one, zero_add, add_zero]
  ring

end ContinuousFlexibility.Statements

