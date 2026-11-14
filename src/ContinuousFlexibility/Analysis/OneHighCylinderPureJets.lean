module

public import ContinuousFlexibility.Analysis.OneHighCylinderSmoothJets
public import ContinuousFlexibility.Analysis.OneHighPeriodicJets
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Actual pure derivatives of a smooth cylinder function

These two towers retain the radial and angular endpoints needed for the
Sobolev norm comparison. They are constructed from the function itself,
including for smooth compositions on the noncompact cylinder.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function Filter
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : ℝ} [Fact (0 < P)]

/-- Continuity may be checked on the ordinary periodic lift. -/
theorem continuous_cylinder_of_lift {f : ℝ × AddCircle P → E}
    (hf : Continuous (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P)))) :
    Continuous f := by
  have hq := (IsOpenQuotientMap.id (X := ℝ)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples P))
  exact hq.isQuotientMap.continuous_iff.mpr hf

private theorem contDiff_parametric_angular_derivative
    {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun θ : ℝ => f (p.1, θ)) p.2) := by
  have ha : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => f (q.1.1, q.2)) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => fderiv ℝ (fun θ : ℝ => f (p.1, θ)) p.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × ℝ) (θ : ℝ) => f (p.1, θ))
      (g := fun p : ℝ × ℝ => p.2) ha contDiff_snd (by simp)
  simpa only [fderiv_apply_one_eq_deriv] using
    hd.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)))

/-- Pure angular differentiation preserves joint smoothness. -/
theorem contDiff_parametric_iteratedDeriv_angular
    {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv n (fun θ => f (p.1, θ)) p.2) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
      have h := contDiff_parametric_angular_derivative ih
      simpa only [iteratedDeriv_succ] using h

/-- Pure radial differentiation preserves joint smoothness. -/
theorem contDiff_parametric_iteratedDeriv_radial
    {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv n (fun r => f (r, p.2)) p.1) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.2, p.1)) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst)
  exact (contDiff_parametric_iteratedDeriv_angular hs n).comp
    (contDiff_snd.prodMk contDiff_fst)

theorem cylinder_lift_periodic (f : ℝ × AddCircle P → E) (r : ℝ) :
    Periodic (fun θ : ℝ => f (r, (θ : AddCircle P))) P := by
  intro θ
  dsimp only
  rw [AddCircle.coe_add_period]

def cylinderRadialJet (f : ℝ × AddCircle P → E) (n : ℕ)
    (p : ℝ × AddCircle P) : E :=
  iteratedDeriv n (fun r : ℝ => f (r, p.2)) p.1

def cylinderAngularJet (f : ℝ × AddCircle P → E) (n : ℕ)
    (p : ℝ × AddCircle P) : E :=
  (periodic_iteratedDeriv (cylinder_lift_periodic f p.1) n).lift p.2

@[simp] theorem cylinderAngularJet_coe_apply (f : ℝ × AddCircle P → E)
    (n : ℕ) (r θ : ℝ) :
    cylinderAngularJet f n (r, (θ : AddCircle P)) =
      iteratedDeriv n (fun y : ℝ => f (r, (y : AddCircle P))) θ :=
  (periodic_iteratedDeriv (cylinder_lift_periodic f r) n).lift_coe θ

@[simp] theorem cylinderRadialJet_zero (f : ℝ × AddCircle P → E) :
    cylinderRadialJet f 0 = f := by
  funext p
  simp only [cylinderRadialJet, iteratedDeriv_zero]

@[simp] theorem cylinderAngularJet_zero (f : ℝ × AddCircle P → E) :
    cylinderAngularJet f 0 = f := by
  funext p
  obtain ⟨r, θ⟩ := p
  refine QuotientAddGroup.induction_on θ ?_
  intro x
  simp only [cylinderAngularJet_coe_apply, iteratedDeriv_zero]

theorem continuous_cylinderRadialJet {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P)))) (n : ℕ) :
    Continuous (cylinderRadialJet f n) := by
  apply continuous_cylinder_of_lift
  exact (contDiff_parametric_iteratedDeriv_radial hf n).continuous

theorem continuous_cylinderAngularJet {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P)))) (n : ℕ) :
    Continuous (cylinderAngularJet f n) := by
  apply continuous_cylinder_of_lift
  simpa only [cylinderAngularJet_coe_apply] using
    (contDiff_parametric_iteratedDeriv_angular hf n).continuous

theorem cylinder_radial_slice_contDiff {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P))))
    (θ : AddCircle P) : ContDiff ℝ ∞ (fun r : ℝ => f (r, θ)) := by
  refine QuotientAddGroup.induction_on θ ?_
  intro x
  exact hf.comp (contDiff_id.prodMk contDiff_const)

theorem cylinder_angular_slice_contDiff {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P))))
    (r : ℝ) : ContDiff ℝ ∞ (fun θ : ℝ => f (r, (θ : AddCircle P))) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

theorem cylinderRadialJet_hasDerivAt {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P))))
    (n : ℕ) (r : ℝ) (θ : AddCircle P) :
    HasDerivAt (fun x : ℝ => cylinderRadialJet f n (x, θ))
      (cylinderRadialJet f (n + 1) (r, θ)) r := by
  have hn : (n : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  simpa only [cylinderRadialJet, iteratedDeriv_succ] using
    ((cylinder_radial_slice_contDiff hf θ).differentiable_iteratedDeriv n hn r).hasDerivAt

theorem cylinderAngularJet_hasDerivAt {f : ℝ × AddCircle P → E}
    (hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (p.1, (p.2 : AddCircle P))))
    (n : ℕ) (r θ : ℝ) :
    HasDerivAt (fun x : ℝ => cylinderAngularJet f n (r, (x : AddCircle P)))
      (cylinderAngularJet f (n + 1) (r, (θ : AddCircle P))) θ := by
  have hn : (n : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  simpa only [cylinderAngularJet_coe_apply, iteratedDeriv_succ] using
    ((cylinder_angular_slice_contDiff hf r).differentiable_iteratedDeriv n hn θ).hasDerivAt

end ContinuousFlexibility.Analysis
