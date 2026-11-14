module

public import ContinuousFlexibility.Analysis.OneHighCylinderPureJets
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Every ordinary smooth cylinder function has its actual mixed jet tower

The jets are the existing pure radial derivatives of the existing pure
angular derivatives. Schwarz symmetry and induction prove the angular
derivative identities; no auxiliary derivative tower is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem cylinder_hasDerivAt_fderiv_apply
    {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f)
    {g : ℝ → ℝ × ℝ} {t : ℝ} {v : ℝ × ℝ}
    (hg : HasDerivAt g v t) (w : ℝ × ℝ) :
    HasDerivAt (fun s => fderiv ℝ f (g s) w)
      (fderiv ℝ (fderiv ℝ f) (g t) v w) t := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hcomp : HasDerivAt (fun s => fderiv ℝ f (g s))
      (fderiv ℝ (fderiv ℝ f) (g t) v) t := by
    simpa only [Function.comp_def] using
      ((hdf.differentiable (by simp) (g t)).hasFDerivAt.comp_hasDerivAt t hg)
  simpa only [map_zero, add_zero] using hcomp.clm_apply (hasDerivAt_const t w)

/-- The two ordinary coordinate derivatives commute for a smooth map
into any real normed space; completeness of the target is unnecessary. -/
private theorem cylinder_deriv_angular_radial_commute
    {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f) (r θ : ℝ) :
    deriv (fun y => deriv (fun x => f (x, y)) r) θ =
      deriv (fun x => deriv (fun y => f (x, y)) θ) r := by
  have hcoord (g : ℝ → ℝ × ℝ) (v : ℝ × ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
      deriv (fun s => f (g s)) t = fderiv ℝ f (g t) v := by
    simpa only [Function.comp_def] using
      ((hf.differentiable (by simp) (g t)).hasFDerivAt.comp_hasDerivAt t hg).deriv
  have hs := (hf.contDiffAt (x := (r, θ))).isSymmSndFDerivAt (by simp)
  calc
    _ = deriv (fun y => fderiv ℝ f (r, y) ((1, 0) : ℝ × ℝ)) θ := by
      apply congrArg (fun h : ℝ → E => deriv h θ)
      funext y
      exact hcoord (fun x => (x, y)) (1, 0) r
        ((hasDerivAt_id r).prodMk (hasDerivAt_const r y))
    _ = fderiv ℝ (fderiv ℝ f) (r, θ) ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) :=
      (cylinder_hasDerivAt_fderiv_apply hf
        ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ)) (1, 0)).deriv
    _ = fderiv ℝ (fderiv ℝ f) (r, θ) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) :=
      hs (0, 1) (1, 0)
    _ = deriv (fun x => fderiv ℝ f (x, θ) ((0, 1) : ℝ × ℝ)) r :=
      (cylinder_hasDerivAt_fderiv_apply hf
        ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ)) (0, 1)).deriv.symm
    _ = _ := by
      apply congrArg (fun h : ℝ → E => deriv h r)
      funext x
      exact (hcoord (fun y => (x, y)) (0, 1) θ
        ((hasDerivAt_const θ x).prodMk (hasDerivAt_id θ))).symm

private theorem cylinder_deriv_angular_iteratedRadial
    {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) (r θ : ℝ) :
    deriv (fun y => iteratedDeriv n (fun x => f (x, y)) r) θ =
      iteratedDeriv n (fun x => deriv (fun y => f (x, y)) θ) r := by
  induction n generalizing r θ with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    calc
      _ = deriv (fun x => deriv (fun y => iteratedDeriv n (fun z => f (z, y)) x) θ) r := by
        simpa only [iteratedDeriv_succ] using
          cylinder_deriv_angular_radial_commute
            (contDiff_parametric_iteratedDeriv_radial hf n) r θ
      _ = _ := by
        rw [iteratedDeriv_succ]
        apply congrArg (fun h : ℝ → E => deriv h r)
        funext x
        exact ih x θ

variable {P : ℝ} [Fact (0 < P)]

theorem contDiff_lift_cylinderAngularJet {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P)))) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => cylinderAngularJet f j (p.1, (p.2 : AddCircle P))) := by
  simpa only [cylinderAngularJet_coe_apply] using
    contDiff_parametric_iteratedDeriv_angular hf j

theorem contDiff_lift_cylinderMixedJet {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P)))) (i j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      cylinderRadialJet (cylinderAngularJet f j) i (p.1, (p.2 : AddCircle P))) :=
  contDiff_parametric_iteratedDeriv_radial (contDiff_lift_cylinderAngularJet hf j) i

theorem cylinderMixedJet_hasDerivAt_angular {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P))))
    (i j : ℕ) (r θ : ℝ) :
    HasDerivAt (fun x : ℝ =>
      cylinderRadialJet (cylinderAngularJet f j) i (r, (x : AddCircle P)))
      (cylinderRadialJet (cylinderAngularJet f (j + 1)) i (r, (θ : AddCircle P))) θ := by
  have hangle : ContDiff ℝ ∞ (fun x : ℝ =>
      cylinderRadialJet (cylinderAngularJet f j) i (r, (x : AddCircle P))) :=
    (contDiff_lift_cylinderMixedJet hf i j).comp (contDiff_const.prodMk contDiff_id)
  apply ((hangle.differentiable (by simp) θ).hasDerivAt).congr_deriv
  dsimp only [cylinderRadialJet]
  apply (cylinder_deriv_angular_iteratedRadial
    (contDiff_lift_cylinderAngularJet hf j) i r θ).trans
  apply congrArg (fun h : ℝ → E => iteratedDeriv i h r)
  funext x
  exact (cylinderAngularJet_hasDerivAt hf j x θ).deriv

/-- The genuine mixed derivative tower of an arbitrary smooth cylinder
function, constructed from the ordinary smoothness of its periodic lift. -/
def CylinderSmoothJet.ofContDiff (f : ℝ × AddCircle P → E)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P)))) :
    CylinderSmoothJet P E where
  jet i j := cylinderRadialJet (cylinderAngularJet f j) i
  continuous i j := continuous_cylinderRadialJet (contDiff_lift_cylinderAngularJet hf j) i
  radial i j r θ :=
    cylinderRadialJet_hasDerivAt (contDiff_lift_cylinderAngularJet hf j) i r θ
  angular i j r θ := cylinderMixedJet_hasDerivAt_angular hf i j r θ

@[simp] theorem CylinderSmoothJet.ofContDiff_jet (f : ℝ × AddCircle P → E)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P))))
    (i j : ℕ) (p : ℝ × AddCircle P) :
    (CylinderSmoothJet.ofContDiff f hf).jet i j p =
      cylinderRadialJet (cylinderAngularJet f j) i p := rfl

@[simp] theorem CylinderSmoothJet.ofContDiff_jet_zero (f : ℝ × AddCircle P → E)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P)))) :
    (CylinderSmoothJet.ofContDiff f hf).jet 0 0 = f := by
  funext p
  simp only [CylinderSmoothJet.ofContDiff_jet, cylinderRadialJet_zero, cylinderAngularJet_zero]

end ContinuousFlexibility.Analysis
