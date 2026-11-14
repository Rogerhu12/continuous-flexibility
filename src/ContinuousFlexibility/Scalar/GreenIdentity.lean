module

public import ContinuousFlexibility.Scalar.Conservation
public import ContinuousFlexibility.Scalar.TypeCorrection

/-!
# Green identity for actual symmetric divergence operators

All derivatives below are the actual coordinate partials on `PolarPoint`.
The integration density is `dr dθ`. Formal symmetry is proved on a finite
rectangle with explicit angular seam and radial conormal boundary conditions;
no closed operator realization or endpoint limit is asserted here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Radial component of the symmetric coefficient matrix applied to `du`. -/
def symmetricNormalFlux (A B u : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  A x * radialPartial u x + B x * angularPartial u x

/-- Angular component of the same flux. -/
def symmetricAngularFlux (B C u : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  B x * radialPartial u x + C x * angularPartial u x

def symmetricDivergence (A B C u : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  radialPartial (symmetricNormalFlux A B u) x +
    angularPartial (symmetricAngularFlux B C u) x

def greenNormalFlux (A B φ ψ : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  φ x * symmetricNormalFlux A B ψ x - ψ x * symmetricNormalFlux A B φ x

def greenAngularFlux (B C φ ψ : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  φ x * symmetricAngularFlux B C ψ x - ψ x * symmetricAngularFlux B C φ x

/-- The rotated Green flux: its exterior derivative is the Green divergence. -/
def symmetricGreenForm (A B C φ ψ : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨fun x => ψ x * symmetricAngularFlux B C φ x -
      φ x * symmetricAngularFlux B C ψ x,
    greenNormalFlux A B φ ψ⟩

theorem contDiffAt_symmetricNormalFlux
    {A B u : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hu : ContDiffAt ℝ ∞ u x) :
    ContDiffAt ℝ ∞ (symmetricNormalFlux A B u) x :=
  (hA.mul (contDiffAt_radialPartial hu (by simp))).add
    (hB.mul (contDiffAt_angularPartial hu (by simp)))

theorem contDiffAt_symmetricAngularFlux
    {B C u : PolarPoint → ℝ} {x : PolarPoint}
    (hB : ContDiffAt ℝ ∞ B x) (hC : ContDiffAt ℝ ∞ C x)
    (hu : ContDiffAt ℝ ∞ u x) :
    ContDiffAt ℝ ∞ (symmetricAngularFlux B C u) x :=
  contDiffAt_symmetricNormalFlux hB hC hu

theorem contDiffAt_symmetricGreenForm
    {A B C φ ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hC : ContDiffAt ℝ ∞ C x) (hφ : ContDiffAt ℝ ∞ φ x)
    (hψ : ContDiffAt ℝ ∞ ψ x) :
    ContDiffAt ℝ ∞ (symmetricGreenForm A B C φ ψ).radial x ∧
      ContDiffAt ℝ ∞ (symmetricGreenForm A B C φ ψ).angular x :=
  ⟨(hψ.mul (contDiffAt_symmetricAngularFlux hB hC hφ)).sub
      (hφ.mul (contDiffAt_symmetricAngularFlux hB hC hψ)),
    (hφ.mul (contDiffAt_symmetricNormalFlux hA hB hψ)).sub
      (hψ.mul (contDiffAt_symmetricNormalFlux hA hB hφ))⟩

/-- Pointwise Green identity, with actual product rules. Symmetry cancels
the first-order cross terms; no equation for either test function is assumed. -/
theorem symmetric_green_identity
    {A B C φ ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hC : ContDiffAt ℝ ∞ C x) (hφ : ContDiffAt ℝ ∞ φ x)
    (hψ : ContDiffAt ℝ ∞ ψ x) :
    φ x * symmetricDivergence A B C ψ x -
        ψ x * symmetricDivergence A B C φ x =
      radialPartial (greenNormalFlux A B φ ψ) x +
        angularPartial (greenAngularFlux B C φ ψ) x := by
  have dφ := hφ.differentiableAt (by simp)
  have dψ := hψ.differentiableAt (by simp)
  have dφr := (contDiffAt_symmetricNormalFlux hA hB hφ).differentiableAt (by simp)
  have dψr := (contDiffAt_symmetricNormalFlux hA hB hψ).differentiableAt (by simp)
  have dφt := (contDiffAt_symmetricAngularFlux hB hC hφ).differentiableAt (by simp)
  have dψt := (contDiffAt_symmetricAngularFlux hB hC hψ).differentiableAt (by simp)
  unfold greenNormalFlux greenAngularFlux symmetricDivergence
  rw [radialPartial_sub
      (f := fun y => φ y * symmetricNormalFlux A B ψ y)
      (g := fun y => ψ y * symmetricNormalFlux A B φ y) (dφ.mul dψr) (dψ.mul dφr),
    angularPartial_sub
      (f := fun y => φ y * symmetricAngularFlux B C ψ y)
      (g := fun y => ψ y * symmetricAngularFlux B C φ y) (dφ.mul dψt) (dψ.mul dφt),
    radialPartial_mul dφ dψr, radialPartial_mul dψ dφr,
    angularPartial_mul dφ dψt, angularPartial_mul dψ dφt]
  simp only [symmetricNormalFlux, symmetricAngularFlux]
  ring

theorem symmetric_green_identity_exterior
    {A B C φ ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hC : ContDiffAt ℝ ∞ C x) (hφ : ContDiffAt ℝ ∞ φ x)
    (hψ : ContDiffAt ℝ ∞ ψ x) :
    φ x * symmetricDivergence A B C ψ x -
        ψ x * symmetricDivergence A B C φ x =
      exteriorCoefficient (symmetricGreenForm A B C φ ψ) x := by
  have dφ := hφ.differentiableAt (by simp)
  have dψ := hψ.differentiableAt (by simp)
  have dφt := (contDiffAt_symmetricAngularFlux hB hC hφ).differentiableAt (by simp)
  have dψt := (contDiffAt_symmetricAngularFlux hB hC hψ).differentiableAt (by simp)
  rw [symmetric_green_identity hA hB hC hφ hψ]
  change _ = radialPartial (greenNormalFlux A B φ ψ) x -
    angularPartial (fun y => ψ y * symmetricAngularFlux B C φ y -
      φ y * symmetricAngularFlux B C ψ y) x
  unfold greenAngularFlux
  rw [angularPartial_sub
      (f := fun y => φ y * symmetricAngularFlux B C ψ y)
      (g := fun y => ψ y * symmetricAngularFlux B C φ y) (dφ.mul dψt) (dψ.mul dφt),
    angularPartial_sub
      (f := fun y => ψ y * symmetricAngularFlux B C φ y)
      (g := fun y => φ y * symmetricAngularFlux B C ψ y) (dψ.mul dφt) (dφ.mul dψt)]
  ring

/-- Rectangle Green symmetry. The angular Green flux matches at the seam,
and the radial Green flux matches at the two ends (zero at each end suffices). -/
theorem integral_symmetric_green_eq_zero
    {A B C φ ψ : PolarPoint → ℝ} {a b c d : ℝ}
    (hA : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ A x)
    (hB : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ B x)
    (hC : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ C x)
    (hφ : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ φ x)
    (hψ : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ ψ x)
    (hseam : ∀ r ∈ uIcc a b,
      greenAngularFlux B C φ ψ (r, d) = greenAngularFlux B C φ ψ (r, c))
    (hends : ∀ θ ∈ uIcc c d,
      greenNormalFlux A B φ ψ (b, θ) = greenNormalFlux A B φ ψ (a, θ)) :
    (∫ r in a..b, ∫ θ in c..d,
      φ (r, θ) * symmetricDivergence A B C ψ (r, θ) -
        ψ (r, θ) * symmetricDivergence A B C φ (r, θ)) = 0 := by
  have hα := fun x hx => contDiffAt_symmetricGreenForm
    (hA x hx) (hB x hx) (hC x hx) (hφ x hx) (hψ x hx)
  have hp : ∀ r ∈ uIcc a b,
      (symmetricGreenForm A B C φ ψ).radial (r, d) =
        (symmetricGreenForm A B C φ ψ).radial (r, c) := by
    intro r hr
    have hs := congrArg Neg.neg (hseam r hr)
    simpa only [greenAngularFlux, symmetricGreenForm, neg_sub] using hs
  have hi := integral_exteriorCoefficient_eq_zero
    (fun x hx => (hα x hx).1.of_le (by simp))
    (fun x hx => (hα x hx).2.of_le (by simp)) hp hends
  calc
    _ = ∫ r in a..b, ∫ θ in c..d,
        exteriorCoefficient (symmetricGreenForm A B C φ ψ) (r, θ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact symmetric_green_identity_exterior
        (hA (r, θ) ⟨hr, hθ⟩) (hB (r, θ) ⟨hr, hθ⟩)
        (hC (r, θ) ⟨hr, hθ⟩) (hφ (r, θ) ⟨hr, hθ⟩) (hψ (r, θ) ⟨hr, hθ⟩)
    _ = 0 := hi

/-- A common Robin multiplier annihilates the boundary Wronskian.
The multiplier can be different at the two radial ends. -/
theorem greenNormalFlux_eq_zero_of_robin
    {A B φ ψ : PolarPoint → ℝ} {x : PolarPoint} {t : ℝ}
    (hφ : symmetricNormalFlux A B φ x = t * φ x)
    (hψ : symmetricNormalFlux A B ψ x = t * ψ x) :
    greenNormalFlux A B φ ψ x = 0 := by
  unfold greenNormalFlux
  rw [hφ, hψ]
  ring

theorem greenNormalFlux_eq_zero_of_dirichlet
    {A B φ ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hφ : φ x = 0) (hψ : ψ x = 0) :
    greenNormalFlux A B φ ψ x = 0 := by
  simp [greenNormalFlux, hφ, hψ]

theorem periodic_greenAngularFlux
    {B C φ ψ : PolarPoint → ℝ} {v : PolarPoint}
    (hB : Function.Periodic B v) (hC : Function.Periodic C v)
    (hφ : Function.Periodic φ v) (hψ : Function.Periodic ψ v) :
    Function.Periodic (greenAngularFlux B C φ ψ) v := by
  intro x
  simp only [greenAngularFlux, symmetricAngularFlux, hφ x, hψ x, hB x, hC x,
    periodic_radialPartial hφ x, periodic_radialPartial hψ x,
    periodic_angularPartial hφ x, periodic_angularPartial hψ x]

/-- Periodic tests and coefficients supply the seam condition. The only
radial boundary restriction is the displayed vanishing conormal Wronskian;
common Robin, Neumann, or Dirichlet test conditions supply it. -/
theorem integral_symmetric_green_eq_zero_of_periodic
    {A B C φ ψ : PolarPoint → ℝ} {a b T : ℝ}
    (hA : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ A x)
    (hB : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ B x)
    (hC : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ C x)
    (hφ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ φ x)
    (hψ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ ψ x)
    (hBp : Function.Periodic B (0, T)) (hCp : Function.Periodic C (0, T))
    (hφp : Function.Periodic φ (0, T)) (hψp : Function.Periodic ψ (0, T))
    (ha : ∀ θ ∈ uIcc 0 T, greenNormalFlux A B φ ψ (a, θ) = 0)
    (hb : ∀ θ ∈ uIcc 0 T, greenNormalFlux A B φ ψ (b, θ) = 0) :
    (∫ r in a..b, ∫ θ in 0..T,
      φ (r, θ) * symmetricDivergence A B C ψ (r, θ) -
        ψ (r, θ) * symmetricDivergence A B C φ (r, θ)) = 0 := by
  apply integral_symmetric_green_eq_zero hA hB hC hφ hψ
  · intro r _
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      periodic_greenAngularFlux hBp hCp hφp hψp (r, 0)
  · intro θ hθ
    rw [hb θ hθ, ha θ hθ]

/-- Actual height coefficients inherit angular translation-periodicity
from the height. Totalized derivatives and quotients cause no exception. -/
theorem periodic_heightCorrectedCoefficients
    (w : ℝ → ℝ) {z : PolarPoint → ℝ} {T : ℝ}
    (hz : Function.Periodic z (0, T)) :
    Function.Periodic (polarLinearA w z) (0, T) ∧
      Function.Periodic (polarLinearB w z) (0, T) ∧
      Function.Periodic (polarCorrectedC w z) (0, T) := by
  have hE : Function.Periodic (profileEnergy w) (0, T) := by
    intro x
    simp only [profileEnergy, Prod.fst_add, add_zero]
  have hk : Function.Periodic (heightRadial z) (0, T) := periodic_radialPartial hz
  have hp : Function.Periodic (heightAngular z) (0, T) := by
    intro x
    simp only [heightAngular, periodic_angularPartial hz x, Prod.fst_add, add_zero]
  have hEr := periodic_radialPartial hE
  have hkr := periodic_radialPartial hk
  have hpr := periodic_radialPartial hp
  have hpt := periodic_angularPartial hp
  have hs : Function.Periodic (polarScale w z) (0, T) := by
    intro x
    simp only [polarScale, polarDiscriminant, hE x, hk x, hp x]
  refine ⟨?_, ?_, ?_⟩ <;> intro x <;>
    simp only [polarLinearA, polarLinearB, polarCorrectedC, Prod.fst_add, add_zero,
      hE x, hEr x, hk x, hp x, hkr x, hpr x, hpt x, hs x]

/-- Local Green identity for the actual corrected height operator. -/
theorem heightCorrected_green_identity
    {w : ℝ → ℝ} {z φ ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiffAt ℝ ∞ w x.1) (hz : ContDiffAt ℝ ∞ z x)
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x)
    (hr : x.1 ≠ 0) (hD : 0 < polarDiscriminant w z x)
    (hQ : heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) ≠ 0) :
    φ x * heightCorrectedDivergence w z ψ x -
        ψ x * heightCorrectedDivergence w z φ x =
      exteriorCoefficient (symmetricGreenForm
        (polarLinearA w z) (polarLinearB w z) (polarCorrectedC w z) φ ψ) x := by
  obtain ⟨hA, hB, _, hC, _, _⟩ := contDiffAt_heightLinearCoefficients hw hz hr hD hQ
  exact symmetric_green_identity_exterior hA hB hC hφ hψ

/-- Vanishing boundary height jets force the actual normal flux to vanish
for every test function, whose boundary height value remains unrestricted.
No division by the vanishing radial coefficient is used. -/
theorem heightCorrected_normalFlux_eq_zero_of_boundary_jets
    (w : ℝ → ℝ) {z : PolarPoint → ℝ} (u : PolarPoint → ℝ) {x : PolarPoint}
    (hk : heightRadial z x = 0)
    (hpr : radialPartial (heightAngular z) x = 0)
    (hpt : angularPartial (heightAngular z) x = 0) :
    symmetricNormalFlux (polarLinearA w z) (polarLinearB w z) u x = 0 := by
  simp [symmetricNormalFlux, polarLinearA, polarLinearB, linearRadial, linearMixed,
    heightQ, hk, hpr, hpt]

/-- Formal symmetry of the actual corrected height operator with ordinary
`dr dθ` density. Its actual coefficient extensions must be smooth on the
rectangle, including its ends. This version allows the radial coefficient
to vanish at flat endpoints. -/
theorem integral_heightCorrected_green_eq_zero
    {w : ℝ → ℝ} {z φ ψ : PolarPoint → ℝ} {a b T : ℝ}
    (hA : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ (polarLinearA w z) x)
    (hB : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ (polarLinearB w z) x)
    (hC : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ (polarCorrectedC w z) x)
    (hφ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ φ x)
    (hψ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ ψ x)
    (hzp : Function.Periodic z (0, T))
    (hφp : Function.Periodic φ (0, T)) (hψp : Function.Periodic ψ (0, T))
    (ha : ∀ θ ∈ uIcc 0 T,
      greenNormalFlux (polarLinearA w z) (polarLinearB w z) φ ψ (a, θ) = 0)
    (hb : ∀ θ ∈ uIcc 0 T,
      greenNormalFlux (polarLinearA w z) (polarLinearB w z) φ ψ (b, θ) = 0) :
    (∫ r in a..b, ∫ θ in 0..T,
      φ (r, θ) * heightCorrectedDivergence w z ψ (r, θ) -
        ψ (r, θ) * heightCorrectedDivergence w z φ (r, θ)) = 0 := by
  obtain ⟨_, hBp, hCp⟩ := periodic_heightCorrectedCoefficients w hzp
  exact integral_symmetric_green_eq_zero_of_periodic hA hB hC hφ hψ
    hBp hCp hφp hψp ha hb

/-- Interior admissibility supplies actual coefficient smoothness. Unlike
the preceding extension-based API, this convenience version is intended
for rectangles on which `Q` stays nonzero, not for flat endpoint collars. -/
theorem integral_heightCorrected_green_eq_zero_of_admissible
    {w : ℝ → ℝ} {z φ ψ : PolarPoint → ℝ} {a b T : ℝ}
    (hw : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ w x.1)
    (hz : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ z x)
    (hφ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ φ x)
    (hψ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ ψ x)
    (hr : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, x.1 ≠ 0)
    (hD : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, 0 < polarDiscriminant w z x)
    (hQ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T,
      heightQ (profileEnergy w x) (heightRadial z x)
        (angularPartial (heightAngular z) x) ≠ 0)
    (hzp : Function.Periodic z (0, T))
    (hφp : Function.Periodic φ (0, T)) (hψp : Function.Periodic ψ (0, T))
    (ha : ∀ θ ∈ uIcc 0 T,
      greenNormalFlux (polarLinearA w z) (polarLinearB w z) φ ψ (a, θ) = 0)
    (hb : ∀ θ ∈ uIcc 0 T,
      greenNormalFlux (polarLinearA w z) (polarLinearB w z) φ ψ (b, θ) = 0) :
    (∫ r in a..b, ∫ θ in 0..T,
      φ (r, θ) * heightCorrectedDivergence w z ψ (r, θ) -
        ψ (r, θ) * heightCorrectedDivergence w z φ (r, θ)) = 0 := by
  have hc := fun x hx => contDiffAt_heightLinearCoefficients
    (hw x hx) (hz x hx) (hr x hx) (hD x hx) (hQ x hx)
  exact integral_heightCorrected_green_eq_zero
    (fun x hx => (hc x hx).1) (fun x hx => (hc x hx).2.1)
    (fun x hx => (hc x hx).2.2.2.1) hφ hψ hzp hφp hψp ha hb

/-- At flat height boundary jets the normal coefficient row vanishes.
Consequently no endpoint value or endpoint derivative condition is imposed
on the two periodic tests. Actual coefficient smoothness across these
degenerate ends is an explicit, separate hypothesis. -/
theorem integral_heightCorrected_green_eq_zero_of_boundary_jets
    {w : ℝ → ℝ} {z φ ψ : PolarPoint → ℝ} {a b T : ℝ}
    (hA : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ (polarLinearA w z) x)
    (hB : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ (polarLinearB w z) x)
    (hC : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ (polarCorrectedC w z) x)
    (hφ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ φ x)
    (hψ : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ ψ x)
    (hzp : Function.Periodic z (0, T))
    (hφp : Function.Periodic φ (0, T)) (hψp : Function.Periodic ψ (0, T))
    (ha : ∀ θ ∈ uIcc 0 T, heightRadial z (a, θ) = 0 ∧
      radialPartial (heightAngular z) (a, θ) = 0 ∧
      angularPartial (heightAngular z) (a, θ) = 0)
    (hb : ∀ θ ∈ uIcc 0 T, heightRadial z (b, θ) = 0 ∧
      radialPartial (heightAngular z) (b, θ) = 0 ∧
      angularPartial (heightAngular z) (b, θ) = 0) :
    (∫ r in a..b, ∫ θ in 0..T,
      φ (r, θ) * heightCorrectedDivergence w z ψ (r, θ) -
        ψ (r, θ) * heightCorrectedDivergence w z φ (r, θ)) = 0 := by
  apply integral_heightCorrected_green_eq_zero hA hB hC hφ hψ hzp hφp hψp
  · intro θ hθ
    obtain ⟨hk, hpr, hpt⟩ := ha θ hθ
    apply greenNormalFlux_eq_zero_of_robin (t := 0)
    · simpa only [zero_mul] using
        heightCorrected_normalFlux_eq_zero_of_boundary_jets w φ hk hpr hpt
    · simpa only [zero_mul] using
        heightCorrected_normalFlux_eq_zero_of_boundary_jets w ψ hk hpr hpt
  · intro θ hθ
    obtain ⟨hk, hpr, hpt⟩ := hb θ hθ
    apply greenNormalFlux_eq_zero_of_robin (t := 0)
    · simpa only [zero_mul] using
        heightCorrected_normalFlux_eq_zero_of_boundary_jets w φ hk hpr hpt
    · simpa only [zero_mul] using
        heightCorrected_normalFlux_eq_zero_of_boundary_jets w ψ hk hpr hpt

end ContinuousFlexibility
