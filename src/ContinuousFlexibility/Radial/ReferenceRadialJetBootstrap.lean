module

public import ContinuousFlexibility.Radial.ReferenceModerateCoefficients
public import ContinuousFlexibility.Radial.ReferenceRadialEndpoint

/-!
# Differentiating the actual radial equation in the weighted spaces

Finite coefficient expressions are built from actual derivatives of w,
1/w, and 1/r. Their formal derivative is proved to be their genuine
derivative on the radial core. Finite solution expressions are then closed
under differentiation by the original inhomogeneous radial equation.
This proves all-order weighted membership from u, u', and the forcing jets,
without assuming any higher-order estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

inductive ReferenceCoefficientExpr where
  | scalar : ℝ → ReferenceCoefficientExpr
  | profile : ℕ → ReferenceCoefficientExpr
  | reciprocalProfile : ℕ → ReferenceCoefficientExpr
  | reciprocalRadius : ℕ → ReferenceCoefficientExpr
  | smooth : {k : ℝ → ℝ // ContDiff ℝ ∞ k} → ℕ → ReferenceCoefficientExpr
  | add : ReferenceCoefficientExpr → ReferenceCoefficientExpr → ReferenceCoefficientExpr
  | mul : ReferenceCoefficientExpr → ReferenceCoefficientExpr → ReferenceCoefficientExpr

def ReferenceCoefficientExpr.eval (D : ReferenceData) : ReferenceCoefficientExpr → ℝ → ℝ
  | .scalar c => fun _ => c
  | .profile n => iteratedDeriv n D.w
  | .reciprocalProfile n => iteratedDeriv n (fun r => (D.w r)⁻¹)
  | .reciprocalRadius n => iteratedDeriv n (fun r : ℝ => r⁻¹)
  | .smooth k n => iteratedDeriv n k.1
  | .add e f => fun r => e.eval D r + f.eval D r
  | .mul e f => fun r => e.eval D r * f.eval D r

def ReferenceCoefficientExpr.formalDeriv : ReferenceCoefficientExpr → ReferenceCoefficientExpr
  | .scalar _ => .scalar 0
  | .profile n => .profile (n + 1)
  | .reciprocalProfile n => .reciprocalProfile (n + 1)
  | .reciprocalRadius n => .reciprocalRadius (n + 1)
  | .smooth k n => .smooth k (n + 1)
  | .add e f => .add e.formalDeriv f.formalDeriv
  | .mul e f => .add (.mul e.formalDeriv f) (.mul e f.formalDeriv)

theorem ReferenceCoefficientExpr.moderate {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (e : ReferenceCoefficientExpr) :
    ReferenceModerate D (e.eval D) := by
  induction e with
  | scalar c => exact ReferenceModerate.const D c
  | profile n => exact referenceModerate_profile_jet hD n
  | reciprocalProfile n => exact referenceModerate_reciprocal_profile_jet hD n
  | reciprocalRadius n => exact referenceModerate_reciprocal_radius_jet hD n
  | smooth k n => exact referenceModerate_smooth_jet hD k.2 n
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem ReferenceCoefficientExpr.hasDerivAt_eval {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (e : ReferenceCoefficientExpr)
    {r : ℝ} (hr : r ∈ radialCore D) :
    HasDerivAt (e.eval D) (e.formalDeriv.eval D r) r := by
  induction e with
  | scalar c => exact hasDerivAt_const r c
  | profile n =>
    have hd := (((referenceModerate_profile_jet hD n).1.differentiableOn (by simp) r hr).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
    simpa only [eval, formalDeriv, iteratedDeriv_succ] using hd
  | reciprocalProfile n =>
    have hd := (((referenceModerate_reciprocal_profile_jet hD n).1.differentiableOn
      (by simp) r hr).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
    simpa only [eval, formalDeriv, iteratedDeriv_succ] using hd
  | reciprocalRadius n =>
    have hd := (((referenceModerate_reciprocal_radius_jet hD n).1.differentiableOn
      (by simp) r hr).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
    simpa only [eval, formalDeriv, iteratedDeriv_succ] using hd
  | smooth k n =>
    have hd := (((referenceModerate_smooth_jet hD k.2 n).1.differentiableOn
      (by simp) r hr).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
    simpa only [eval, formalDeriv, iteratedDeriv_succ] using hd
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

def referenceDriftExpr : ReferenceCoefficientExpr :=
  .mul (.scalar (-1)) (.mul (.profile 1) (.reciprocalProfile 0))

def referencePotentialExpr (J : ℝ) : ReferenceCoefficientExpr :=
  .mul (.scalar J) (.mul (.profile 1) (.mul (.reciprocalProfile 0) (.reciprocalRadius 0)))

theorem reference_radial_second_derivative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u f : ℝ → ℝ} {J : ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D))
    (he : ∀ r ∈ radialCore D, radialJacobi J D.w u r = f r)
    {r : ℝ} (hr : r ∈ radialCore D) :
    deriv (deriv u) r = referenceDriftExpr.eval D r * deriv u r +
      (referencePotentialExpr J).eval D r * u r + (D.w r)⁻¹ * f r := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hw := (hgeom.2.2.1.1.differentiable (by simp) r).hasDerivAt
  have hdu : ContDiffOn ℝ ∞ (deriv u) (radialCore D) :=
    (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hu |>.2
  have hdu' := ((hdu.differentiableOn (by simp) r hr).differentiableAt
    (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  have hflux := hw.mul hdu'
  change HasDerivAt (fun t => D.w t * deriv u t)
    (deriv D.w r * deriv u r + D.w r * deriv (deriv u) r) r at hflux
  have hEq := he r hr
  rw [radialJacobi, hflux.deriv] at hEq
  have hwr : D.w r ≠ 0 := (hgeom.2.2.2.2.1 r hr).ne'
  have hrr : r ≠ 0 := (hgeom.1.trans hr.1).ne'
  simp only [referenceDriftExpr, referencePotentialExpr, ReferenceCoefficientExpr.eval,
    iteratedDeriv_zero, iteratedDeriv_one]
  field_simp [hwr, hrr] at hEq ⊢
  nlinarith only [hEq]

inductive ReferenceSolutionExpr where
  | solution : ReferenceSolutionExpr
  | normal : ReferenceSolutionExpr
  | forcingJet : ℕ → ReferenceSolutionExpr
  | add : ReferenceSolutionExpr → ReferenceSolutionExpr → ReferenceSolutionExpr
  | scale : ReferenceCoefficientExpr → ReferenceSolutionExpr → ReferenceSolutionExpr

def ReferenceSolutionExpr.eval (D : ReferenceData) (u f : ℝ → ℝ) :
    ReferenceSolutionExpr → ℝ → ℝ
  | .solution => u
  | .normal => deriv u
  | .forcingJet n => iteratedDeriv n f
  | .add e g => fun r => e.eval D u f r + g.eval D u f r
  | .scale c e => fun r => c.eval D r * e.eval D u f r

def ReferenceSolutionExpr.formalDeriv (J : ℝ) : ReferenceSolutionExpr → ReferenceSolutionExpr
  | .solution => .normal
  | .normal =>
      .add (.add (.scale referenceDriftExpr .normal) (.scale (referencePotentialExpr J) .solution))
        (.scale (.reciprocalProfile 0) (.forcingJet 0))
  | .forcingJet n => .forcingJet (n + 1)
  | .add e g => .add (e.formalDeriv J) (g.formalDeriv J)
  | .scale c e => .add (.scale c.formalDeriv e) (.scale c (e.formalDeriv J))

theorem ReferenceSolutionExpr.rapid {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {u f : ℝ → ℝ} (hu : ReferenceRapid D u) (hd : ReferenceRapid D (deriv u))
    (hf : ∀ n, ReferenceRapid D (iteratedDeriv n f)) (e : ReferenceSolutionExpr) :
    ReferenceRapid D (e.eval D u f) := by
  induction e with
  | solution => exact hu
  | normal => exact hd
  | forcingJet n => exact hf n
  | add e g he hg => exact he.add hD.choose_spec.2.1 hg
  | scale c e he => exact he.mul_moderate hD.choose_spec.2.1 (c.moderate hD)

theorem ReferenceSolutionExpr.hasDerivAt_eval {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u f : ℝ → ℝ} {J : ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D))
    (hf : ContDiffOn ℝ ∞ f (radialCore D))
    (he : ∀ r ∈ radialCore D, radialJacobi J D.w u r = f r)
    (e : ReferenceSolutionExpr) {r : ℝ} (hr : r ∈ radialCore D) :
    HasDerivAt (e.eval D u f) ((e.formalDeriv J).eval D u f r) r := by
  induction e with
  | solution =>
    exact ((hu.differentiableOn (by simp) r hr).differentiableAt
      (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  | normal =>
    have hdu : ContDiffOn ℝ ∞ (deriv u) (radialCore D) :=
      (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hu |>.2
    have hd := ((hdu.differentiableOn (by simp) r hr).differentiableAt
      (isOpen_Ioo.mem_nhds hr)).hasDerivAt
    apply hd.congr_deriv
    simpa only [formalDeriv, eval, ReferenceCoefficientExpr.eval, iteratedDeriv_zero] using
      reference_radial_second_derivative hD hu he hr
  | forcingJet n =>
    have hfn := reference_contDiffOn_iteratedDeriv isOpen_Ioo hf n
    have hd := ((hfn.differentiableOn (by simp) r hr).differentiableAt
      (isOpen_Ioo.mem_nhds hr)).hasDerivAt
    simpa only [formalDeriv, eval, iteratedDeriv_succ] using hd
  | add e g he hg => exact he.add hg
  | scale c e he => exact (c.hasDerivAt_eval hD hr).mul he

def referenceSolutionJetExpr (J : ℝ) : ℕ → ReferenceSolutionExpr
  | 0 => .solution
  | n + 1 => (referenceSolutionJetExpr J n).formalDeriv J

theorem referenceSolutionJetExpr_eqOn {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u f : ℝ → ℝ} {J : ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D))
    (hf : ContDiffOn ℝ ∞ f (radialCore D))
    (he : ∀ r ∈ radialCore D, radialJacobi J D.w u r = f r) (n : ℕ) :
    EqOn (iteratedDeriv n u) ((referenceSolutionJetExpr J n).eval D u f) (radialCore D) := by
  induction n with
  | zero => intro r _; rfl
  | succ n ih =>
    intro r hr
    have heq : iteratedDeriv n u =ᶠ[𝓝 r] (referenceSolutionJetExpr J n).eval D u f := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact ((referenceSolutionJetExpr J n).hasDerivAt_eval hD hu hf he hr).deriv

theorem reference_radial_jets_rapid {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u f : ℝ → ℝ} {J : ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D))
    (hf : ContDiffOn ℝ ∞ f (radialCore D))
    (he : ∀ r ∈ radialCore D, radialJacobi J D.w u r = f r)
    (huW : ReferenceRapid D u) (hdW : ReferenceRapid D (deriv u))
    (hfW : ∀ n, ReferenceRapid D (iteratedDeriv n f)) (n : ℕ) :
    ReferenceRapid D (iteratedDeriv n u) := by
  apply ((referenceSolutionJetExpr J n).rapid hD huW hdW hfW).of_eqOn
  intro r hr
  exact (referenceSolutionJetExpr_eqOn hD hu hf he n hr).symm

/-- The same genuine differentiation proof applies to every finite solution
expression, including the border commutator. -/
def ReferenceSolutionExpr.jetExpr (J : ℝ) (e : ReferenceSolutionExpr) :
    ℕ → ReferenceSolutionExpr
  | 0 => e
  | n + 1 => (e.jetExpr J n).formalDeriv J

theorem ReferenceSolutionExpr.jetExpr_eqOn {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u f : ℝ → ℝ} {J : ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D))
    (hf : ContDiffOn ℝ ∞ f (radialCore D))
    (he : ∀ r ∈ radialCore D, radialJacobi J D.w u r = f r)
    (e : ReferenceSolutionExpr) (n : ℕ) :
    EqOn (iteratedDeriv n (e.eval D u f)) ((e.jetExpr J n).eval D u f)
      (radialCore D) := by
  induction n with
  | zero => intro r _; rfl
  | succ n ih =>
    intro r hr
    have heq : iteratedDeriv n (e.eval D u f) =ᶠ[𝓝 r]
        (e.jetExpr J n).eval D u f := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact ((e.jetExpr J n).hasDerivAt_eval hD hu hf he hr).deriv

theorem ReferenceSolutionExpr.jets_rapid {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u f : ℝ → ℝ} {J : ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D))
    (hf : ContDiffOn ℝ ∞ f (radialCore D))
    (he : ∀ r ∈ radialCore D, radialJacobi J D.w u r = f r)
    (huW : ReferenceRapid D u) (hdW : ReferenceRapid D (deriv u))
    (hfW : ∀ n, ReferenceRapid D (iteratedDeriv n f))
    (e : ReferenceSolutionExpr) (n : ℕ) :
    ReferenceRapid D (iteratedDeriv n (e.eval D u f)) := by
  apply ((e.jetExpr J n).rapid hD huW hdW hfW).of_eqOn
  intro r hr
  exact (e.jetExpr_eqOn hD hu hf he n hr).symm

end ContinuousFlexibility.Radial
