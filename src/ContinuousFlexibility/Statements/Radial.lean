import ContinuousFlexibility.Statements.DeepTailOperator
import ContinuousFlexibility.Radial.OscillatorCompactCore
import ContinuousFlexibility.Radial.CentralSpectralInverse
import ContinuousFlexibility.Radial.MorseModel
import ContinuousFlexibility.Radial.FourierOrthogonality
import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# Typed targets for the radial existence engine

This file states R01--R12 and X01; it proves none of their existence claims.
The records below contain functions, partitions and operators, never arbitrary
proposition fields.  In particular `RadialReferenceStatement` is a target, not
a theorem producing a reference.  The source density is ordinary `dr`, and
the angular average is normalized.  Closed forms and distribution graphs are
spelled out independently of the already constructed Hermite graph.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory Real
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

abbrev RadialL2 := Radial.HermiteL2
abbrev RadialSource := (PolarPoint → ℝ) × ℝ
abbrev RadialUnknown := (PolarPoint → ℝ) × ℝ

def radialAngularMean (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ

def radialJet : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => deriv (radialJet n f)

def radialS (n : ℕ) : ℝ := (2 / 3 : ℝ) * (n : ℝ) ^ 3
def radialQ (n : ℕ) : ℝ := (n : ℝ) ^ (5 / 2 : ℝ) * log (Real.exp 1 + n)
def radialH (n : ℕ) : ℝ := exp (-radialS n)
def radialE (n : ℕ) : ℝ := exp (radialQ n)

/-- Pure data; none of the radial existence conclusions is a field. -/
structure ReferenceData where
  a : ℝ
  b : ℝ
  w : ℝ → ℝ
  phi : ℝ → ℝ
  chi : ℝ → ℝ
  chiLeft : ℝ → ℝ
  cells : ℕ → Set ℝ
  localizer : ℕ → ℝ → ℝ
  cellIndex : ℕ → ℕ

def radialCore (D : ReferenceData) : Set ℝ := Ioo D.a D.b

def radialAnnulus (D : ReferenceData) : Set PolarPoint :=
  radialCore D ×ˢ Set.univ

def radialPhysicalMeasure (D : ReferenceData) : Measure PolarPoint :=
  volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi))

def radialHilbertMeasure (D : ReferenceData) : Measure ℝ :=
  (volume.restrict (radialCore D)).withDensity
    (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2))

/-- This is literally `L'_(2,w)[w chi] phi`, not a freely chosen border. -/
def referenceColumn (D : ReferenceData) (r : ℝ) : ℝ :=
  Radial.radialJacobi 4 (fun t => D.w t * D.chi t) D.phi r

/-- Positive modes use the paper's orthonormal `sqrt 2 * cos(j theta)`.
The zero mode is `radialAngularMean`, not `referenceMode 0`. -/
def referenceMode (u : PolarPoint → ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  radialAngularMean (fun θ => u (r, θ) * Radial.cosineMode j θ)

def referenceRow (D : ReferenceData) (u : PolarPoint → ℝ) : ℝ :=
  ∫ r in D.a..D.b, referenceColumn D r * referenceMode u 2 r

def EndpointFlat (D : ReferenceData) (u : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ u ∧ ∀ r, r ≤ D.a ∨ D.b ≤ r → u r = 0

def RadialProfileGeometry (D : ReferenceData) : Prop :=
  0 < D.a ∧ D.a < D.b ∧ EndpointFlat D D.w ∧ EndpointFlat D D.phi ∧
  (∀ r ∈ radialCore D, 0 < D.w r) ∧
  (∃ r ∈ radialCore D, D.phi r ≠ 0) ∧
  (∀ r ∈ radialCore D, deriv D.w r = 0 → deriv (deriv D.w) r ≠ 0)

def RadialPartition (D : ReferenceData) : Prop :=
  (∀ m, ContDiff ℝ ∞ (D.localizer m)) ∧
  (∀ m r, 0 ≤ D.localizer m r) ∧
  (∀ m, Function.support (D.localizer m) ⊆ D.cells m) ∧
  (∀ m, D.cells m ⊆ radialCore D) ∧
  (∀ r ∈ radialCore D, Summable (fun m => D.localizer m r) ∧
    (∑' m, D.localizer m r) = 1) ∧
  (∃ B : ℕ, ∀ r, Set.Finite {m | D.localizer m r ≠ 0} ∧
    {m | D.localizer m r ≠ 0}.ncard ≤ B)

/-- Quantitatively separated circles available inside the actual radial cells.
This is geometric data required of the R05 construction, not an assumption
that a circle trace or its right inverse has already been constructed.
The lower width pays only a fixed coefficient power at each fixed order. -/
def RadialTraceScaffold (D : ReferenceData) : Prop :=
  ∃ centers widths : ℕ → ℝ, ∃ K : ℝ, 0 < K ∧
    (∀ m, centers m ∈ D.cells m ∧ 0 < widths m ∧
      K⁻¹ * radialE (D.cellIndex m) ^ (-K) ≤ widths m ∧
      Icc (centers m - widths m) (centers m + widths m) ⊆ D.cells m) ∧
    Pairwise (fun m n : ℕ =>
      Disjoint (Ioo (centers m - widths m) (centers m + widths m))
        (Ioo (centers n - widths n) (centers n + widths n)))

/-- Uniform cell bounds usable before any reference inverse exists. -/
def AccumulatingProfileBounds (D : ReferenceData) (C : ℕ → ℝ) : Prop :=
  RadialProfileGeometry D ∧ RadialPartition D ∧
  (∀ s, 0 < C s) ∧
  (∀ m, (D.cells m).Nonempty) ∧
  (∀ N : ℕ, Set.Finite {m | D.cellIndex m ≤ N}) ∧
  (∀ K : Set ℝ, IsCompact K → K ⊆ radialCore D →
    Set.Finite {m | (D.cells m ∩ K).Nonempty}) ∧
  (∀ m r, r ∈ D.cells m →
    (C 0)⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2) ≤ min (r - D.a) (D.b - r) ∧
      min (r - D.a) (D.b - r) ≤ C 0 * exp (-(D.cellIndex m : ℝ) ^ 2)) ∧
  (∀ m r, r ∈ D.cells m →
    exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) - C 0 * (D.cellIndex m : ℝ) ^ 2) ≤ D.w r) ∧
  (∀ m r, r ∈ D.cells m → ∀ s,
    |radialJet s D.w r| ≤ C s *
      exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) + C s * (D.cellIndex m : ℝ) ^ 2)) ∧
  (∀ m r, r ∈ D.cells m → ∀ s,
    |radialJet s (fun t => (D.w t)⁻¹) r| ≤ C s * radialE (D.cellIndex m) ^ (C s)) ∧
  (∀ m, ∃ l h : ℝ, D.cells m ⊆ Icc l h ∧
    h - l ≤ C 0 * exp (-(D.cellIndex m : ℝ) ^ 2)) ∧
  (∀ a b ε : ℝ, 0 < a → 0 < b → 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ n, radialE n ^ a * exp (b * (n : ℝ) ^ 2) ≤ K * exp (ε * radialS n)) ∧
  RadialTraceScaffold D

def IsAccumulatingProfile (D : ReferenceData) : Prop :=
  ∃ C : ℕ → ℝ, AccumulatingProfileBounds D C

def WeakRadialDerivative (u d : RadialL2) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x : ℝ, u x * deriv φ x) = -(∫ x : ℝ, d x * φ x)

def WeakSchrodingerGraph (V : ℝ → ℝ) (u v : RadialL2) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x : ℝ, v x * φ x) =
      ∫ x : ℝ, u x * (-deriv (deriv φ) x + V x * φ x)

/-- Actual weak derivative and actual potential-weighted L², with its graph norm. -/
def SchrodingerEnergyLift (V : ℝ → ℝ) : Set (RadialL2 × RadialL2 × RadialL2) :=
  {p | WeakRadialDerivative p.1 p.2.1 ∧
    (p.2.2 : ℝ → ℝ) =ᵐ[volume]
      (fun x => sqrt (1 + |V x|) * p.1 x)}

def SchrodingerEnergyCore (V : ℝ → ℝ) : Set (RadialL2 × RadialL2 × RadialL2) :=
  {p | ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    (p.1 : ℝ → ℝ) =ᵐ[volume] φ ∧
    (p.2.1 : ℝ → ℝ) =ᵐ[volume] deriv φ ∧
    (p.2.2 : ℝ → ℝ) =ᵐ[volume] (fun x => sqrt (1 + |V x|) * φ x)}

/-- The associated form operator, not an arbitrary relation supplied as input. -/
def SchrodingerFormGraph (V : ℝ → ℝ) (u v : RadialL2) : Prop :=
  ∃ d q : RadialL2, (u, d, q) ∈ SchrodingerEnergyLift V ∧
    ∀ p ∈ SchrodingerEnergyLift V,
      Integrable (fun x : ℝ => V x * u x * p.1 x) volume ∧
      ⟪v, p.1⟫_ℝ = ⟪d, p.2.1⟫_ℝ + ∫ x : ℝ, V x * u x * p.1 x

/-- Explicit closed-form/Friedrichs identification required by R03/R04. -/
def ActualClosedFormRealization (V : ℝ → ℝ) : Prop :=
  (∃ c : ℝ, ∀ x, -c ≤ V x) ∧
  IsClosed (SchrodingerEnergyLift V) ∧
  closure (SchrodingerEnergyCore V) = SchrodingerEnergyLift V ∧
  (∀ u v, WeakSchrodingerGraph V u v ↔ SchrodingerFormGraph V u v)

def WeakResolventBound (V : ℝ → ℝ) (E C : ℝ) : Prop :=
  ∃ G : RadialL2 →L[ℝ] RadialL2, ‖G‖ ≤ C ∧
    (∀ f, WeakSchrodingerGraph V (G f) (f + E • G f)) ∧
    (∀ u f, WeakSchrodingerGraph V u (f + E • u) → G f = u)

def centralPotential (j x : ℝ) : ℝ :=
  j ^ 2 * x ^ 2 + Radial.centralRadiusA ^ 2 - j ^ 2 * Radial.centralOscillatorA

def centralUpsilon (x : ℝ) : ℝ :=
  deriv Radial.centralRadius x / Radial.centralRadius x

def CentralFullDifferentialSpectrum : Prop :=
  ∀ j : ℝ, 0 < j → ActualClosedFormRealization (centralPotential j) ∧
    ∀ u v : RadialL2,
      WeakSchrodingerGraph (centralPotential j) u v ↔
        ∀ n, Radial.hermiteCoefficient j v n =
          Radial.centralSpectralLevel j n * Radial.hermiteCoefficient j u n

def CentralReducedInverse : Prop :=
  ∃ G : RadialL2 →L[ℝ] RadialL2, ‖G‖ = (1 / 4 : ℝ) ∧
    (∀ f, WeakSchrodingerGraph (centralPotential 2) (G f)
      (f - Radial.centralGroundProjection f)) ∧
    (∀ u f, WeakSchrodingerGraph (centralPotential 2) u f →
      G f = u - Radial.centralGroundProjection u)

/-- A bound for multiplication on both sides, on the actual dense test core. -/
def CentralWeightedInverseBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ψ : ℝ → ℝ,
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    ∀ f : RadialL2, ((f : ℝ → ℝ) =ᵐ[volume] ψ) →
    ∃ F u q : RadialL2,
      ((F : ℝ → ℝ) =ᵐ[volume] fun x => centralUpsilon x * ψ x) ∧
      WeakSchrodingerGraph (centralPotential (2 * n)) u
        (if n = 1 then F - Radial.centralGroundProjection F else F) ∧
      (n = 1 → Radial.centralGroundProjection u = 0) ∧
      ((q : ℝ → ℝ) =ᵐ[volume] fun x => centralUpsilon x * u x) ∧ ‖q‖ ≤ C * ‖f‖

def CentralAllOrderAsymptotics : Prop :=
  ∀ s : ℕ, ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧
    (∀ x, R ≤ x →
      |radialJet s (fun y => centralUpsilon y -
        (y + Radial.centralRadiusA + (Radial.centralRadiusAlpha - 1) / y)) x| ≤
          C / |x| ^ (3 + s)) ∧
    (∀ x, x ≤ -R →
      |radialJet s (fun y => centralUpsilon y -
        (-y + Radial.centralRadiusA - Radial.centralRadiusAlpha / y)) x| ≤
          C / |x| ^ (3 + s))

def QuadraticIrrational (t : ℝ) : Prop :=
  Irrational t ∧ ∃ a b c : ℤ, a ≠ 0 ∧ (a : ℝ) * t ^ 2 + b * t + c = 0

def morsePotential (j A B x : ℝ) : ℝ := -j ^ 2 * Radial.morseRho A B x

def morseLevel (j A B : ℝ) (m : ℕ) : ℝ :=
  j ^ 2 * B - ((j * sqrt A - 1) / 2 - m) ^ 2

def ActualEigenvalue (V : ℝ → ℝ) (E : ℝ) : Prop :=
  ∃ u : RadialL2, u ≠ 0 ∧ WeakSchrodingerGraph V u (E • u)

/-- The Weyl essential-spectrum criterion uses actual weak differential pairs. -/
def EssentialWeylValue (V : ℝ → ℝ) (E : ℝ) : Prop :=
  ∃ u v : ℕ → RadialL2,
    (∀ n, ‖u n‖ = 1 ∧ WeakSchrodingerGraph V (u n) (v n)) ∧
    (∀ h : RadialL2, Tendsto (fun n => ⟪u n, h⟫_ℝ) atTop (𝓝 0)) ∧
    Tendsto (fun n => ‖v n - E • u n‖) atTop (𝓝 0)

def MorseFullDifferentialSpectrum (j A B : ℝ) : Prop :=
  ActualClosedFormRealization (morsePotential j A B) ∧
  (∀ E : ℝ, E < j ^ 2 * B →
    (ActualEigenvalue (morsePotential j A B) E ↔
      ∃ m : ℕ, (m : ℝ) < (j * sqrt A - 1) / 2 ∧ E = morseLevel j A B m)) ∧
  (∀ E : ℝ, EssentialWeylValue (morsePotential j A B) E ↔ j ^ 2 * B ≤ E) ∧
  (∀ E : ℝ, E < j ^ 2 * B → ActualEigenvalue (morsePotential j A B) E →
    ∃ u : RadialL2, u ≠ 0 ∧ ∀ v : RadialL2,
      WeakSchrodingerGraph (morsePotential j A B) v (E • v) ↔ ∃ c : ℝ, v = c • u)

def morseTravel (A B : ℝ) : ℝ :=
  ∫ x in -log ((1 + sqrt (1 - 4 * B / A)) / 2)..
    -log ((1 - sqrt (1 - 4 * B / A)) / 2), sqrt (Radial.morseRho A B x)

/-- R01, manuscript §5 `eq:rad-eq-rm13`; statement only. -/
def R01Statement : Prop :=
  (∀ a r : ℝ, ∀ V : ℝ → ℝ, 0 < r → Differentiable ℝ V →
    DifferentiableAt ℝ (deriv V) (log r) →
    deriv (Radial.gaugeLift a V) r = Radial.gaugeFirst a V (deriv V) r ∧
    deriv (deriv (Radial.gaugeLift a V)) r = r ^ (a - 2) *
      (a * (a - 1) * V (log r) + (2 * a - 1) * deriv V (log r) +
        deriv (deriv V) (log r))) ∧
  ∀ a y : ℝ, ∀ w V : ℝ → ℝ,
    DifferentiableAt ℝ w (exp y) → Differentiable ℝ V →
    DifferentiableAt ℝ (deriv V) y →
    Radial.logGaugeEquation a w V y = exp ((a + 1) * y) *
      Radial.radialJacobi a w (Radial.gaugeLift a V) (exp y)

abbrev LiouvilleModelL2 (R : ℝ → ℝ) (scale : ℝ) :=
  MeasureTheory.Lp ℝ 2 (volume.withDensity (fun x =>
    ENNReal.ofReal (12 * scale * (deriv R x / R x) ^ 2)))

abbrev LiouvillePhysicalL2 (R w : ℝ → ℝ) :=
  MeasureTheory.Lp ℝ 2 ((volume.restrict (Set.range R)).withDensity
    (fun r => ENNReal.ofReal (12 * w r / r ^ 2)))

def LiouvilleFullTransport (R s w X : ℝ → ℝ) (scale : ℝ) : Prop :=
  (∃ U : LiouvilleModelL2 R scale ≃ₗᵢ[ℝ] LiouvillePhysicalL2 R w,
    (∀ ψ, ((U ψ : LiouvillePhysicalL2 R w) : ℝ → ℝ) =ᵐ[
      (volume.restrict (Set.range R)).withDensity
        (fun r => ENNReal.ofReal (12 * w r / r ^ 2))]
      (fun r => ψ (X r) / s (X r))) ∧
    (∀ u, ((U.symm u : LiouvilleModelL2 R scale) : ℝ → ℝ) =ᵐ[
      volume.withDensity (fun x => ENNReal.ofReal (12 * scale * (deriv R x / R x) ^ 2))]
      (fun x => s x * u (R x)))) ∧
  (∀ u ψ f : ℝ → ℝ, (∀ x, u (R x) = ψ x / s x) →
    IntegrableOn (fun r => u r * f r) (Set.range R) volume →
    Integrable (fun x => ψ x * (deriv R x / s x * f (R x))) volume ∧
    (∫ r in Set.range R, u r * f r) =
      ∫ x : ℝ, ψ x * (deriv R x / s x * f (R x)))

/-- R02, manuscript §4 `eq:rad-eq-sc0`, `eq:rad-eq-ha2`; statement only. -/
def R02Statement : Prop :=
  ∀ R s : ℝ → ℝ, ∀ scale : ℝ, 0 < scale → ContDiff ℝ ∞ R → ContDiff ℝ ∞ s →
    (∀ x, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x) →
    ∃ X w h : ℝ → ℝ,
      (∀ x, X (R x) = x) ∧ (∀ r ∈ Set.range R, R (X r) = r) ∧
      ContDiffOn ℝ ∞ X (Set.range R) ∧ ContDiffOn ℝ ∞ w (Set.range R) ∧
      ContDiffOn ℝ ∞ h (Set.range R) ∧
      (∀ x, w (R x) = scale * s x ^ 2 * deriv R x ∧ 0 < w (R x)) ∧
      (∀ r ∈ Set.range R, HasDerivAt h (w r) r) ∧
      (∀ ψ u : ℝ → ℝ, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ u →
        (∀ x, u (R x) = ψ x / s x) → ∀ j x,
          Radial.radialJacobi (j ^ 2) w u (R x) =
            -(scale * s x / deriv R x) * Radial.liouvilleSchrodinger (j ^ 2) R s ψ x) ∧
      (∀ x, (12 * w (R x) / R x ^ 2) * deriv R x =
        12 * scale * (deriv R x / R x) ^ 2 * s x ^ 2) ∧
      LiouvilleFullTransport R s w X scale

def centralHilbertMeasure (scale : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun r =>
    ENNReal.ofReal (12 * Radial.centralRadialProfile scale r / r ^ 2))

abbrev CentralRadialL2 (scale : ℝ) := MeasureTheory.Lp ℝ 2 (centralHilbertMeasure scale)

def CentralAuxiliaryGraph (scale : ℝ) (g : ℝ → ℝ)
    (U F : CentralRadialL2 scale × ℝ) : Prop :=
  (∫ r in Ioi (0 : ℝ), g r * U.1 r) = F.2 ∧
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    Function.support ψ ⊆ Ioi (0 : ℝ) →
    (∫ r in Ioi (0 : ℝ), U.1 r *
      Radial.radialJacobi 4 (Radial.centralRadialProfile scale) ψ r) -
      U.2 * (∫ r in Ioi (0 : ℝ), g r * ψ r) =
    -(∫ r in Ioi (0 : ℝ),
      (12 * Radial.centralRadialProfile scale r / r ^ 2) * F.1 r * ψ r)

def CentralCompactAuxiliaryBorderStatement : Prop :=
  ∃ g₀ : ℝ → ℝ, ContDiff ℝ ∞ g₀ ∧ HasCompactSupport g₀ ∧
    Function.support g₀ ⊆ Ioi (0 : ℝ) ∧
    (∫ r in Ioi (0 : ℝ), g₀ r * Radial.centralKernelHeight r) = 1 ∧
    ∃ C : ℝ, 0 < C ∧ ∀ scale : ℝ, 0 < scale →
      IntegrableOn (fun r => (sqrt scale * g₀ r) ^ 2 /
        (12 * Radial.centralRadialProfile scale r / r ^ 2)) (Ioi 0) volume ∧
      IntegrableOn (fun r => (12 * Radial.centralRadialProfile scale r / r ^ 2) *
        (Radial.centralKernelHeight r / sqrt scale) ^ 2) (Ioi 0) volume ∧
      (∫ r in Ioi (0 : ℝ),
        (sqrt scale * g₀ r) ^ 2 / (12 * Radial.centralRadialProfile scale r / r ^ 2)) ≤ C ∧
      (∫ r in Ioi (0 : ℝ),
        (12 * Radial.centralRadialProfile scale r / r ^ 2) *
          (Radial.centralKernelHeight r / sqrt scale) ^ 2) ≤ C ∧
      ∃ G : (CentralRadialL2 scale × ℝ) →L[ℝ] (CentralRadialL2 scale × ℝ),
        ‖G‖ ≤ C ∧
        (∀ F, CentralAuxiliaryGraph scale (fun r => sqrt scale * g₀ r) (G F) F) ∧
        (∀ U F, CentralAuxiliaryGraph scale (fun r => sqrt scale * g₀ r) U F → G F = U)

def CentralRadialContact : Prop :=
  Set.range Radial.centralRadius = Ioi (0 : ℝ) ∧
  (∀ scale : ℝ, 0 < scale → ∀ X : ℝ,
    Radial.centralRadialProfile scale (Radial.centralRadius X) =
      scale * Radial.centralDensityRoot X ^ 2 * deriv Radial.centralRadius X) ∧
  (∀ scale r : ℝ, 0 < scale → 0 < r →
    Radial.radialJacobi 4 (Radial.centralRadialProfile scale) Radial.centralKernelHeight r = 0) ∧
  (∀ X : ℝ,
    Radial.centralRadius X * deriv Radial.centralKernelHeight (Radial.centralRadius X) /
      Radial.centralKernelHeight (Radial.centralRadius X) =
        (Radial.centralRadiusA - 2 * X) / centralUpsilon X) ∧
  (∀ X : ℝ,
    Radial.centralRadius X * deriv (Radial.centralRadialProfile 1) (Radial.centralRadius X) /
      Radial.centralRadialProfile 1 (Radial.centralRadius X) =
        (X ^ 2 - Radial.centralOscillatorA) / centralUpsilon X ^ 2) ∧
  Tendsto (fun X => (Radial.centralRadiusA - 2 * X) / centralUpsilon X) atBot (𝓝 2) ∧
  Tendsto (fun X => (Radial.centralRadiusA - 2 * X) / centralUpsilon X) atTop (𝓝 (-2)) ∧
  Tendsto (fun X => (X ^ 2 - Radial.centralOscillatorA) / centralUpsilon X ^ 2) atBot (𝓝 1) ∧
  Tendsto (fun X => (X ^ 2 - Radial.centralOscillatorA) / centralUpsilon X ^ 2) atTop (𝓝 1)

/-- R03, §4 central oscillator, including the actual closed form, not only levels. -/
def R03Statement : Prop :=
  CentralFullDifferentialSpectrum ∧ CentralReducedInverse ∧
  CentralWeightedInverseBounds ∧ CentralAllOrderAsymptotics ∧
  CentralCompactAuxiliaryBorderStatement ∧ CentralRadialContact ∧
  (∀ n : ℕ, 2 ≤ n → WeakResolventBound (centralPotential (2 * n)) 0
    (2 / Radial.centralGapDelta)) ∧
  (∀ u : RadialL2, WeakSchrodingerGraph (centralPotential 2) u 0 ↔
    ∃ c : ℝ, u = c • Radial.hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0) ∧
  (∀ scale : ℝ, 0 < scale → ContDiffOn ℝ ∞ (Radial.centralRadialProfile scale) (Ioi 0) ∧
    ∀ r : ℝ, 0 < r → 0 < Radial.centralRadialProfile scale r) ∧
  (∀ x, 0 < deriv Radial.centralRadius x ∧
    Radial.liouvilleRho Radial.centralRadius Radial.centralDensityRoot x =
      Radial.centralOscillatorA - x ^ 2) ∧
  (∀ c : ℝ, 0 < c → ∀ r : ℝ, 0 < r →
    (deriv (Radial.centralRadialProfile c) r = 0 →
      deriv (deriv (Radial.centralRadialProfile c)) r ≠ 0)) ∧
  Radial.quadraticTravelIntegral Radial.centralOscillatorA = Real.pi / (2 * sqrt 2) ∧
  (∀ k : ℕ, 1 ≤ k → (1 / 8 : ℝ) / k ≤
    |sin ((k : ℝ) * Radial.quadraticTravelIntegral Radial.centralOscillatorA)|)

/-- R04, §4 Morse spectrum, actual zero resolvent and independent return gap. -/
def R04Statement : Prop :=
  ∀ d : ℕ, 1 < d → (¬ ∃ n : ℕ, n ^ 2 = d) →
    let A := ((d : ℝ) ^ (-1 / 2 : ℝ) + 2 * (d : ℝ) ^ (-9 / 2 : ℝ)) ^ 2
    let B := (d : ℝ) ^ (-9 : ℝ)
    A > 4 * B ∧ 0 < B ∧
    (∀ j : ℕ, 2 ≤ j → MorseFullDifferentialSpectrum j A B ∧
      WeakResolventBound (morsePotential j A B) 0 (8 * (d : ℝ) ^ 9)) ∧
    morseTravel A B = Real.pi / (2 * sqrt d) ∧
    (∀ k : ℕ, 1 ≤ k → (3 * (k : ℝ) * sqrt d)⁻¹ ≤ |sin (k * morseTravel A B)|)

def referenceCellSquare (D : ReferenceData) (m : ℕ) (f : PolarPoint → ℝ) : ℝ :=
  ∫ r in D.a..D.b, radialAngularMean (fun θ => (D.localizer m r * f (r, θ)) ^ 2)

def sourceCellSquare (D : ReferenceData) (γ M : ℝ)
    (f : PolarPoint → ℝ) (m : ℕ) : ℝ :=
  exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
    referenceCellSquare D m f

def outputCellSquare (D : ReferenceData) (γ M : ℝ)
    (f : PolarPoint → ℝ) (m : ℕ) : ℝ :=
  exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
    referenceCellSquare D m f

/-- Actual local `L²` membership, including almost-everywhere strong measurability.
This is the source and output domain used by the maximal weak graph. -/
def RadialCellIntegrable (D : ReferenceData) (f : PolarPoint → ℝ) : Prop :=
  ∀ m, MemLp (fun x : PolarPoint => D.localizer m x.1 * f x) 2
    (radialPhysicalMeasure D)

def SourceMember (D : ReferenceData) (γ M : ℝ) (F : RadialSource) : Prop :=
  RadialCellIntegrable D F.1 ∧ Summable (sourceCellSquare D γ M F.1) ∧
  Function.Periodic F.1 (0, Real.pi) ∧ (∀ r θ, F.1 (r, -θ) = F.1 (r, θ)) ∧
  IntervalIntegrable (fun r => radialAngularMean (fun θ => F.1 (r, θ))) volume D.a D.b ∧
  (∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ))) = 0

def sourceNormSquare (D : ReferenceData) (γ M : ℝ) (F : RadialSource) : ℝ :=
  F.2 ^ 2 + ∑' m, sourceCellSquare D γ M F.1 m

def outputRemainder (D : ReferenceData) (aL : ℝ) (U : RadialUnknown) : PolarPoint → ℝ :=
  fun x => U.1 x - aL * D.chiLeft x.1

def OutputRealization (D : ReferenceData) (γ M aL : ℝ) (U : RadialUnknown) : Prop :=
  RadialCellIntegrable D (outputRemainder D aL U) ∧
    Summable (outputCellSquare D γ M (outputRemainder D aL U)) ∧
    Function.Periodic U.1 (0, Real.pi) ∧ (∀ r θ, U.1 (r, -θ) = U.1 (r, θ))

def OutputMember (D : ReferenceData) (γ M : ℝ) (U : RadialUnknown) : Prop :=
  ∃ aL : ℝ, OutputRealization D γ M aL U

def outputNormSquare (D : ReferenceData) (γ M aL : ℝ) (U : RadialUnknown) : ℝ :=
  aL ^ 2 + U.2 ^ 2 + ∑' m, outputCellSquare D γ M (outputRemainder D aL U) m

def RadialRepresentativeEq (D : ReferenceData) (U V : RadialUnknown) : Prop :=
  U.2 = V.2 ∧ U.1 =ᵐ[radialPhysicalMeasure D] V.1

def RadialTest (D : ReferenceData) (ψ : PolarPoint → ℝ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ Function.Periodic ψ (0, 2 * Real.pi) ∧
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, ∀ θ, ψ (r, θ) = 0

def radialWeakPairing (D : ReferenceData) (u : PolarPoint → ℝ)
    (ψ : PolarPoint → ℝ) : ℝ :=
  ∫ r in D.a..D.b, radialAngularMean (fun θ =>
    u (r, θ) * Radial.radialPDE D.w (fun t φ => ψ (t, φ)) r θ)

/-- The maximum distributional graph is defined by the actual differential
expression, not as the range of a proposed inverse. -/
def ReferenceGraph (D : ReferenceData) (γ M₀ M₁ : ℝ)
    (U : RadialUnknown) (F : RadialSource) : Prop :=
  OutputMember D γ M₁ U ∧ SourceMember D γ M₀ F ∧
  referenceRow D U.1 = F.2 ∧
  ∀ ψ, RadialTest D ψ →
    radialWeakPairing D U.1 ψ + U.2 *
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceColumn D r * Radial.cosineMode 2 θ * ψ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * ψ (r, θ))

def ReferenceInverseProperties (D : ReferenceData) (γ M₀ M₁ : ℝ)
    (G : RadialSource → RadialUnknown) : Prop :=
  (∀ F, SourceMember D γ M₀ F → ReferenceGraph D γ M₀ M₁ (G F) F) ∧
  (∀ U F, ReferenceGraph D γ M₀ M₁ U F → RadialRepresentativeEq D (G F) U) ∧
  (∀ F K, SourceMember D γ M₀ F → SourceMember D γ M₀ K → ∀ c d : ℝ,
    RadialRepresentativeEq D (G (c • F + d • K)) (c • G F + d • G K)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F → ∃ aL : ℝ,
    OutputRealization D γ M₁ aL (G F) ∧
      outputNormSquare D γ M₁ aL (G F) ≤ C ^ 2 * sourceNormSquare D γ M₀ F)

def BoundedReferenceInverse (D : ReferenceData) (γ M₀ M₁ : ℝ) : Prop :=
  ∃ G : RadialSource → RadialUnknown, ReferenceInverseProperties D γ M₀ M₁ G

def SmoothAdmissibleField (D : ReferenceData) (U : RadialUnknown) : Prop :=
  ContDiff ℝ ∞ U.1 ∧ Function.Periodic U.1 (0, Real.pi) ∧
    ∃ aL : ℝ, (∀ r, r ≤ D.a → ∀ θ, U.1 (r, θ) = aL) ∧
      (∀ r, D.b ≤ r → ∀ θ, U.1 (r, θ) = 0)

def ReferenceSmoothCoreClosure (D : ReferenceData) (γ M₀ M₁ : ℝ) : Prop :=
  ∀ U F, ReferenceGraph D γ M₀ M₁ U F →
    ∃ Uₙ : ℕ → RadialUnknown, ∃ Fₙ : ℕ → RadialSource, ∃ aₙ : ℕ → ℝ,
      (∀ n, ReferenceGraph D γ M₀ M₁ (Uₙ n) (Fₙ n) ∧ SmoothAdmissibleField D (Uₙ n) ∧
        OutputRealization D γ M₁ (aₙ n) (Uₙ n - U)) ∧
      Tendsto (fun n => sourceNormSquare D γ M₀ (Fₙ n - F)) atTop (𝓝 0) ∧
      Tendsto (fun n => outputNormSquare D γ M₁ (aₙ n) (Uₙ n - U)) atTop (𝓝 0)

def ReferenceGraphClosed (D : ReferenceData) (γ M₀ M₁ : ℝ) : Prop :=
  ∀ (U : RadialUnknown) (F : RadialSource) (Uₙ : ℕ → RadialUnknown)
    (Fₙ : ℕ → RadialSource) (aₙ : ℕ → ℝ),
    (∀ n : ℕ, ReferenceGraph D γ M₀ M₁ (Uₙ n) (Fₙ n)) →
    OutputMember D γ M₁ U → SourceMember D γ M₀ F →
    (∀ n, OutputRealization D γ M₁ (aₙ n) (Uₙ n - U)) →
    Tendsto (fun n => sourceNormSquare D γ M₀ (Fₙ n - F)) atTop (𝓝 0) →
    Tendsto (fun n => outputNormSquare D γ M₁ (aₙ n) (Uₙ n - U)) atTop (𝓝 0) →
    ReferenceGraph D γ M₀ M₁ U F

def ReferenceGreenReciprocity (D : ReferenceData) (γ M₀ M₁ : ℝ) : Prop :=
  ∀ U V F K, ReferenceGraph D γ M₀ M₁ U F → ReferenceGraph D γ M₀ M₁ V K →
    IntegrableOn (fun x : PolarPoint => U.1 x * K.1 x)
      (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume ∧
    IntegrableOn (fun x : PolarPoint => F.1 x * V.1 x)
      (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume ∧
    (∫ r in D.a..D.b, radialAngularMean (fun θ => U.1 (r, θ) * K.1 (r, θ))) +
      U.2 * K.2 =
    (∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * V.1 (r, θ))) +
      F.2 * V.2

def WeakNormalDerivative (D : ReferenceData) (u d : PolarPoint → ℝ) : Prop :=
  ∀ ψ, RadialTest D ψ →
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * radialPartial ψ (r, θ))) =
      -(∫ r in D.a..D.b, radialAngularMean (fun θ => d (r, θ) * ψ (r, θ)))

def WeakAngularDerivative (D : ReferenceData) (u d : PolarPoint → ℝ) : Prop :=
  ∀ ψ, RadialTest D ψ →
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * angularPartial ψ (r, θ))) =
      -(∫ r in D.a..D.b, radialAngularMean (fun θ => d (r, θ) * ψ (r, θ)))

def FirstNormalInverseEstimate (D : ReferenceData) (γ M₀ M₁ : ℝ)
    (G : RadialSource → RadialUnknown) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ F fθ, SourceMember D γ M₀ F →
    WeakAngularDerivative D F.1 fθ → SourceMember D γ M₀ (fθ, 0) →
    ∃ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur ∧
      OutputRealization D γ M₁ 0 (ur, 0) ∧
      outputNormSquare D γ M₁ 0 (ur, 0) ≤ C ^ 2 *
        (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0))

def NaturalRadialNull (D : ReferenceData) (j : ℕ) (u : ℝ → ℝ) : Prop :=
  MemLp u 2 (radialHilbertMeasure D) ∧
    ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ radialCore D →
      (∫ r in D.a..D.b, u r * Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r) = 0

def RadialNaturalKernels (D : ReferenceData) : Prop :=
  (∀ r ∈ radialCore D, Radial.radialJacobi 4 D.w D.phi r = 0) ∧
  (∀ u, NaturalRadialNull D 2 u ↔
    ∃ c : ℝ, u =ᵐ[radialHilbertMeasure D] fun r => c * D.phi r) ∧
  (∀ n : ℕ, 2 ≤ n → ∀ u, NaturalRadialNull D (2 * n) u →
    u =ᵐ[radialHilbertMeasure D] (fun _ => 0))

def NegativeRadialComponent (D : ReferenceData) (l h : ℝ) : Prop :=
  D.a < l ∧ l < h ∧ h < D.b ∧ deriv D.w l = 0 ∧ deriv D.w h = 0 ∧
    ∀ r ∈ Ioo l h, deriv D.w r < 0

def radialTravel (D : ReferenceData) (l h : ℝ) : ℝ :=
  ∫ r in l..h, sqrt (-(deriv D.w r) / (r * D.w r))

def RadialReturnMargins (D : ReferenceData) : Prop :=
  (∀ r ∈ radialCore D, deriv D.w r < 0 →
    ∃ l h : ℝ, NegativeRadialComponent D l h ∧ r ∈ Ioo l h) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ l h, NegativeRadialComponent D l h →
    QuadraticIrrational (radialTravel D l h / Real.pi) ∧
    ∃ m : ℕ, Ioo l h ⊆ D.cells m ∧ ∃ c : ℝ, 0 < c ∧
      c⁻¹ ≤ radialE (D.cellIndex m) ^ C ∧
      ∀ k : ℕ, 1 ≤ k → c / k ≤ |sin (k * radialTravel D l h)|

def RadialTrueBorder (D : ReferenceData) : Prop :=
  ContDiff ℝ ∞ D.chi ∧ HasCompactSupport D.chi ∧
    Function.support D.chi ⊆ {r | r ∈ radialCore D ∧ 0 < deriv D.w r} ∧
    (∫ r in D.a..D.b, referenceColumn D r * D.phi r) = 1 ∧
    ContDiff ℝ ∞ D.chiLeft ∧
    (∃ ε : ℝ, 0 < ε ∧ (∀ r ∈ Ioo D.a (D.a + ε), D.chiLeft r = 1) ∧
      (∀ r ∈ Ioo (D.b - ε) D.b, D.chiLeft r = 0))

def referenceBeta : ℝ := 3 / 4

/-- All three exponents use one profile, border, natural graph and inverse. -/
def IsRadialReference (D : ReferenceData) : Prop :=
  IsAccumulatingProfile D ∧ RadialNaturalKernels D ∧ RadialReturnMargins D ∧
    RadialTrueBorder D ∧ ∃ ε M₀ M₁ : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∃ G : RadialSource → RadialUnknown,
        ∀ γ : ℝ, γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε →
          ReferenceInverseProperties D γ M₀ M₁ G ∧
          ReferenceGraphClosed D γ M₀ M₁ ∧ ReferenceSmoothCoreClosure D γ M₀ M₁ ∧
          ReferenceGreenReciprocity D γ M₀ M₁ ∧ FirstNormalInverseEstimate D γ M₀ M₁ G

/-- A subtype of actual data satisfying the explicitly defined specification.
No inhabitant of this type is asserted in this file. -/
def RadialReference := {D : ReferenceData // IsRadialReference D}

def RadialReferenceStatement : Prop := Nonempty RadialReference

/-! ## Accumulating actual Morse cells (R05) -/

structure MorseChainData where
  index : ℕ
  d : ℕ → ℕ
  radius : Bool → ℕ → ℝ → ℝ
  leftX : Bool → ℕ → ℝ
  rightX : Bool → ℕ → ℝ
  joinLeft : Bool → ℕ → ℝ
  joinRight : Bool → ℕ → ℝ

def morseChainA (T : MorseChainData) (n : ℕ) : ℝ :=
  ((T.d n : ℝ) ^ (-1 / 2 : ℝ) + 2 * (T.d n : ℝ) ^ (-9 / 2 : ℝ)) ^ 2

def morseChainB (T : MorseChainData) (n : ℕ) : ℝ := (T.d n : ℝ) ^ (-9 : ℝ)

def morseChainAmplitude (T : MorseChainData) (σ : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-(n : ℝ) ^ (5 / 2 : ℝ)) * ∏ k ∈ Finset.Icc T.index n, σ k

/-- Right turning point of the actual Morse coefficient, using its smaller
root in the variable `exp (-X)`. -/
def morseChainRightTurn (T : MorseChainData) (n : ℕ) : ℝ :=
  -log ((1 - sqrt (1 - 4 * morseChainB T n / morseChainA T n)) / 2)

/-- The mass interval ends at the right turning point, before the long cap. -/
def morseChainMassEnd (T : MorseChainData) (right : Bool) (n : ℕ) : ℝ :=
  T.radius right n (morseChainRightTurn T n)

/-- The cap is followed by the next glue in increasing radius. The first
left cell has only its retained cap in this resistance interval. -/
def morseChainResistanceEnd (T : MorseChainData) (right : Bool) (n : ℕ) : ℝ :=
  if right then T.joinRight right n
  else if T.index < n then T.joinRight right (n - 1)
  else T.radius right n (T.rightX right n)

/-- The inward endpoint of a cell in the outward order on its side. -/
def morseChainSeam (T : MorseChainData) (right : Bool) (n : ℕ) : ℝ :=
  T.radius right n (if right then T.leftX right n else T.rightX right n)

def morseChainBlock (T : MorseChainData) (right : Bool) (n : ℕ) : Set ℝ :=
  uIcc (morseChainSeam T right n) (morseChainSeam T right (n + 1))

/-- The seam collar is small compared with both incident blocks and the
distance to either flat endpoint. The first seam uses the middle interval. -/
def morseChainSeamCollar (T : MorseChainData) (D : ReferenceData)
    (right : Bool) (n : ℕ) : ℝ :=
  let seam := morseChainSeam T right n
  let inwardLength := if T.index < n then |seam - morseChainSeam T right (n - 1)|
    else morseChainSeam T true T.index - morseChainSeam T false T.index
  let outwardLength := |morseChainSeam T right (n + 1) - seam|
  min (min (seam - D.a) (D.b - seam)) (min inwardLength outwardLength) / 16

def morseChainLocalizerRegion (T : MorseChainData) (D : ReferenceData)
    (right : Bool) (n : ℕ) : Set ℝ :=
  let seam := morseChainSeam T right n
  let next := morseChainSeam T right (n + 1)
  let collar := morseChainSeamCollar T D right n
  let nextCollar := morseChainSeamCollar T D right (n + 1)
  if right then Icc (seam - collar) (next + nextCollar)
  else Icc (next - nextCollar) (seam + collar)

/-- The same retained cell geometry for every height choice, using the fixed
initial slope and cap length constants of the retained-cell construction. -/
def MorseChainRetainedGeometry (T : MorseChainData) : Prop :=
  ∀ (right : Bool) (n : ℕ), T.index ≤ n →
    let A := morseChainA T n
    let B := morseChainB T n
    let turn := morseChainRightTurn T n
    let r := T.radius right n
    0 < B ∧ 4 * B < A ∧
    T.leftX right n = -log (3 / 2) ∧
    T.leftX right n < turn ∧ turn < T.rightX right n ∧
    T.rightX right n = turn + (1 / 100 : ℝ) / A ^ 4 ∧
    deriv r turn = (1 / 100 : ℝ) * A ^ 5 * r turn

def MorseChainRealization (T : MorseChainData) (σ : ℕ → ℝ)
    (D : ReferenceData) (C : ℕ → ℝ) : Prop :=
  (∀ n, T.index ≤ n → exp ((n : ℝ) ^ 2) ≤ T.d n ∧
    (¬ ∃ k : ℕ, k ^ 2 = T.d n) ∧
    ∀ k : ℕ, exp ((n : ℝ) ^ 2) ≤ k → k < T.d n → ∃ m : ℕ, m ^ 2 = k) ∧
  MorseChainRetainedGeometry T ∧
  (∀ side n, T.index ≤ n →
    ContDiff ℝ ∞ (T.radius side n) ∧ T.leftX side n < T.rightX side n ∧
    ∀ X ∈ Icc (T.leftX side n) (T.rightX side n),
      0 < deriv (T.radius side n) X ∧
      deriv (deriv (T.radius side n)) X =
        -Radial.morseRho (morseChainA T n) (morseChainB T n) X * T.radius side n X ∧
      D.w (T.radius side n X) =
        morseChainAmplitude T σ n * deriv (T.radius side n) X) ∧
  (∀ side n, T.index ≤ n → T.joinLeft side n < T.joinRight side n ∧
    T.joinLeft side n = (if side then T.radius side n (T.rightX side n)
      else T.radius side (n + 1) (T.rightX side (n + 1))) ∧
    T.joinRight side n = (if side then T.radius side (n + 1) (T.leftX side (n + 1))
      else T.radius side n (T.leftX side n)) ∧
    T.joinRight side n - T.joinLeft side n ≤ C 0 * (morseChainA T n) ^ 12 ∧
    ∀ r ∈ Ioo (T.joinLeft side n) (T.joinRight side n),
      2 / r ≤ deriv D.w r / D.w r) ∧
  (∀ side n, T.index ≤ n →
    T.radius side n '' Icc (T.leftX side n) (T.rightX side n) ⊆ radialCore D) ∧
  (T.radius false T.index (T.rightX false T.index) <
    T.radius true T.index (T.leftX true T.index)) ∧
  (∀ side : Bool,
    Tendsto (fun n => T.radius side n (T.leftX side n)) atTop
      (𝓝 (if side then D.b else D.a)) ∧
    Tendsto (fun n => T.radius side n (T.rightX side n)) atTop
      (𝓝 (if side then D.b else D.a))) ∧
  (∀ m, T.index < D.cellIndex m → ∃ right : Bool,
    D.cells m ⊆ morseChainLocalizerRegion T D right (D.cellIndex m)) ∧
  (∀ (right : Bool) (n : ℕ), T.index ≤ n →
    ∀ r ∈ morseChainBlock T right n,
      ∃ m : ℕ, D.cellIndex m = n ∧ r ∈ D.cells m) ∧
  AccumulatingProfileBounds D C

def morseCellMass (T : MorseChainData) (D : ReferenceData) (side : Bool) (n : ℕ) : ℝ :=
  ∫ r in T.radius side n (T.leftX side n)..morseChainMassEnd T side n,
    D.w r * r ^ 6

def morseCellResistance (T : MorseChainData) (D : ReferenceData)
    (side : Bool) (n : ℕ) : ℝ :=
  ∫ r in T.radius side n (T.leftX side n)..morseChainMassEnd T side n,
    (D.w r * r ^ 8)⁻¹

def morseJoinMass (T : MorseChainData) (D : ReferenceData) (side : Bool) (n : ℕ) : ℝ :=
  ∫ r in morseChainMassEnd T side n..morseChainResistanceEnd T side n, D.w r * r ^ 6

def morseJoinResistance (T : MorseChainData) (D : ReferenceData)
    (side : Bool) (n : ℕ) : ℝ :=
  ∫ r in morseChainMassEnd T side n..morseChainResistanceEnd T side n, (D.w r * r ^ 8)⁻¹

def MorseMassResistanceBounds (T : MorseChainData) (σ : ℕ → ℝ)
    (D : ReferenceData) (C : ℕ → ℝ) : Prop :=
  ∀ side n, T.index ≤ n →
    morseChainAmplitude T σ n * morseChainA T n ^ 2 / C 0 ≤ morseCellMass T D side n ∧
    morseCellMass T D side n ≤ C 0 * morseChainAmplitude T σ n * morseChainA T n ^ 2 ∧
    morseCellResistance T D side n ≤ C 0 / morseChainAmplitude T σ n *
      log (morseChainA T n / morseChainB T n) ∧
    morseJoinMass T D side n ≤ C 0 * morseChainAmplitude T σ n * morseChainA T n ^ 6 ∧
    (morseChainAmplitude T σ n)⁻¹ * morseChainA T n ^ (-4 : ℝ) / C 0 ≤
      morseJoinResistance T D side n ∧
    morseJoinResistance T D side n ≤
      C 0 * (morseChainAmplitude T σ n)⁻¹ * morseChainA T n ^ (-4 : ℝ)

/-- R05, §5 actual cells, all height choices and all fixed jet orders. -/
def R05Statement : Prop :=
  ∀ initial : ℕ, ∃ T : MorseChainData, initial ≤ T.index ∧
    ∃ C : ℕ → ℝ, ∃ family : (ℕ → ℝ) → ReferenceData,
      (∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) → MorseChainRealization T σ (family σ) C ∧
        MorseMassResistanceBounds T σ (family σ) C) ∧
      (∀ σ τ, (family σ).a = (family τ).a ∧ (family σ).b = (family τ).b ∧
        (family σ).cells = (family τ).cells)

/-! ## Continuous tail form, its inverse and natural line (R06) -/

-- The scalar operator definitions are in `Statements.DeepTailOperator`.

def tailPhysicalRadius (right : Bool) (x : ℝ) : ℝ :=
  exp (if right then x else -x)

def TailPhysicalCellAt (D : ReferenceData) (right : Bool)
    (index : ℕ) (x : ℝ) : Prop :=
  ∃ m : ℕ, D.cellIndex m = index ∧ tailPhysicalRadius right x ∈ D.cells m

/-- Physical labels on the outward edges. On the left the mass and glue
belong to one block, and the following long cap belongs to the next block.
A left entrance can start at the cap or include the preceding glue. -/
def TailPhysicalLocalization (D : ReferenceData) (T : DeepTailData)
    (right : Bool) (start : ℕ) : Prop :=
  if right then
    T.entrance = T.node 0 ∧
      ∀ n x, x ∈ Ioo (T.node n) (T.node (n + 1)) →
        TailPhysicalCellAt D right (start + n) x
  else
    (∀ n, ∃ capStart : ℝ,
      T.massEnd n < capStart ∧ capStart < T.node (n + 1) ∧
      ∀ x ∈ Ioo (T.node n) (T.node (n + 1)),
        TailPhysicalCellAt D right
          (if x < capStart then start + n else start + n + 1) x) ∧
    ((T.entrance < T.node 0 ∧
        ∀ x ∈ Ico T.entrance (T.node 0), TailPhysicalCellAt D right start x) ∨
      (0 < start ∧ ∃ capStart : ℝ,
        T.entrance < capStart ∧ capStart < T.node 0 ∧
        (∀ x ∈ Ico T.entrance capStart, TailPhysicalCellAt D right (start - 1) x) ∧
        ∀ x ∈ Ico capStart (T.node 0), TailPhysicalCellAt D right start x))

def TailPhysicalRelation (D : ReferenceData) (T : DeepTailData)
    (right : Bool) (j start : ℕ) : Prop :=
  T.Λ = (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1) ∧
  T.endpoint = (if right then log D.b else -log D.a) ∧
  (∀ x ∈ Ioo T.entrance T.endpoint,
    tailPhysicalRadius right x ∈ radialCore D ∧
    T.p x = (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
      (2 * (j : ℝ) ^ 2) * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x) ∧
  TailPhysicalLocalization D T right start ∧
  (∃ C : ℝ, 0 < C ∧ ∀ n,
    exp (2 * ((start + n : ℕ) : ℝ) ^ 2 -
      C * (((start + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + n : ℕ))) ≤
      T.Λ * tailMass T (n + 1) * tailResistance T n)

def TailPhysicalFlatConclusion (D : ReferenceData) (T : DeepTailData)
    (right : Bool) (j start : ℕ) : Prop :=
  ∃ u v : ℝ → ℝ, TailNaturalEquation T u ∧
    (∃ x ∈ Ioo T.entrance T.endpoint, u x ≠ 0) ∧ ContDiff ℝ ∞ v ∧
    (∀ x ∈ Ioo T.entrance T.endpoint,
      v (tailPhysicalRadius right x) =
        (tailPhysicalRadius right x / (if right then D.b else D.a)) ^ ((j : ℝ) ^ 2) * u x) ∧
    (∀ x ∈ Ioo T.entrance T.endpoint,
      Radial.radialJacobi ((j : ℝ) ^ 2) D.w v (tailPhysicalRadius right x) = 0) ∧
    (∀ s : ℕ, radialJet s v (if right then D.b else D.a) = 0) ∧
    (∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n x,
      x ∈ Ioo (T.node n) (T.node (n + 1)) →
      |radialJet s v (tailPhysicalRadius right x)| ≤
        C * radialE (start + n) ^ C * exp (-radialS (start + n)))

abbrev HeightRatios := {σ : ℕ → ℝ // ∀ n, σ n ∈ Icc (1 : ℝ) 2}

def DeepTailParameterContinuity (η₀ K₀ : ℝ) : Prop :=
  ∀ family : HeightRatios → DeepTailData,
    (∀ σ, DeepTailHypotheses (family σ) ∧ (family σ).η ≤ η₀ ∧ K₀ ≤ (family σ).K) →
    (∀ σ τ, (family σ).entrance = (family τ).entrance ∧
      (family σ).endpoint = (family τ).endpoint ∧
      (family σ).node = (family τ).node ∧ (family σ).Λ = (family τ).Λ ∧
      (family σ).η = (family τ).η ∧ (family σ).K = (family τ).K) →
    (∀ k : ℕ, ContinuousOn
      (fun z : HeightRatios × ℝ => radialJet k (family z.1).p z.2)
      {z | z.2 ∈ Ico (family z.1).entrance (family z.1).endpoint}) →
    ∃ u : HeightRatios → ℝ → ℝ,
      (∀ σ, TailNaturalEquation (family σ) (u σ) ∧
        u σ (family σ).entrance = 1) ∧
      Continuous (fun σ => deriv (u σ) (family σ).entrance)

def TailPhysicalSourceIdentity (D : ReferenceData) (T : DeepTailData)
    (right : Bool) (j : ℕ) : Prop :=
  ∀ V u : ℝ → ℝ, ContDiff ℝ ∞ V → ContDiff ℝ ∞ u →
    (∀ x ∈ Ioo T.entrance T.endpoint,
      u (tailPhysicalRadius right x) =
        (tailPhysicalRadius right x / (if right then D.b else D.a)) ^ ((j : ℝ) ^ 2) * V x) →
    ∀ x ∈ Ioo T.entrance T.endpoint,
      Radial.radialJacobi ((j : ℝ) ^ 2) D.w u (tailPhysicalRadius right x) =
        -((tailPhysicalRadius right x / (if right then D.b else D.a)) ^ ((j : ℝ) ^ 2) *
          D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x ^ 2) *
        (-(T.p x)⁻¹ * deriv (fun y => T.p y * deriv V y) x - T.Λ * V x)

/-- R06, §5: one actual form realization, strong finite-wall limits and a
unique natural endpoint line; not an abstract inverse postulate. -/
def R06Statement : Prop :=
  ∃ C η₀ K₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ η₀ < 1 ∧ 1 < K₀ ∧
  (∀ T : DeepTailData, DeepTailHypotheses T → T.η ≤ η₀ → K₀ ≤ T.K →
    TailFormIdentification T T.endpoint ∧
    (∀ n, TailFormIdentification T (T.node (n + 1))) ∧
    ∃ G : DeepTailL2 T →L[ℝ] DeepTailL2 T,
      ‖G‖ ≤ C / T.Λ ∧
      (∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f)) ∧
      (∀ u f, TailFriedrichsGraph T T.endpoint u (f + T.Λ • u) → G f = u) ∧
      (∃ Gₙ Pₙ : ℕ → (DeepTailL2 T →L[ℝ] DeepTailL2 T),
        (∀ n f, ((Pₙ n f : DeepTailL2 T) : ℝ → ℝ) =ᵐ[deepTailMeasure T]
          fun x => if x < T.node (n + 1) then f x else 0) ∧
        (∀ n f, TailFriedrichsGraph T (T.node (n + 1)) (Gₙ n (Pₙ n f))
          (Pₙ n f + T.Λ • Gₙ n (Pₙ n f))) ∧
        (∀ f, Tendsto (fun n => Gₙ n (Pₙ n f)) atTop (𝓝 (G f)))) ∧
      TailNaturalLineAndKernel T ∧ TailGreenKernel T G) ∧
  (∀ D T right j start, IsAccumulatingProfile D → DeepTailHypotheses T →
    T.η ≤ η₀ → K₀ ≤ T.K →
    TailPhysicalRelation D T right j start →
    TailPhysicalFlatConclusion D T right j start ∧ TailPhysicalSourceIdentity D T right j) ∧
  DeepTailParameterContinuity η₀ K₀

end ContinuousFlexibility.Statements



