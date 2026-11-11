import ContinuousFlexibility.Scalar.GreenIdentity
import ContinuousFlexibility.Scalar.NormalizedConservation
import ContinuousFlexibility.Geometry.FlatDevelopment

/-!
# Exact scalar milestone propositions

These declarations are *targets*, not assumed axioms and not existence proofs.
Every differential is an actual mathlib derivative of an actual function.
The node correspondence is the original manuscript Section 3.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- S01, Section 3, `eq:height-jet-notation`: positivity, both diagonal
factors, and the actual coframe quadratic identity. -/
def S01Statement : Prop :=
  ∀ r E k p : ℝ, 0 < r → 0 < E →
    (RemainderPositive r E k p ↔ 0 < heightDiscriminant E k p) ∧
    (0 < heightDiscriminant E k p ↔ k ^ 2 / E + p ^ 2 < 1) ∧
    (0 < heightDiscriminant E k p →
      0 < E - k ^ 2 ∧ 0 < 1 - p ^ 2 ∧
      ∀ x y : ℝ, coframeOne E k p x ^ 2 + coframeTwo r k p x y ^ 2 =
        remainderQuadratic r E k p x y)

/-- S02, `eq:cart-determinant-identity`: the residual term and its
correction, with the source and square-root normalization written out. -/
def S02Statement : Prop :=
  (∀ r E w wr k p kr pr pt : ℝ, r ≠ 0 → 0 < heightDiscriminant E k p →
    let D := heightDiscriminant E k p
    let t := inverseDThreeHalves D
    linearRadial E k pt t * linearAngular r E (2 * w * wr) k kr t -
        linearMixed E pr t ^ 2 =
      (w * wr / r) / D ^ 2 + E * t *
        scaledCoordinateResidual r E (2 * w * wr) k p kr pr pt t) ∧
  (∀ r E w wr k p kr pr pt : ℝ, r ≠ 0 → 0 < heightDiscriminant E k p →
    heightQ E k pt ≠ 0 →
    let D := heightDiscriminant E k p
    let t := inverseDThreeHalves D
    linearRadial E k pt t * correctedAngular r E (2 * w * wr) k p kr pr pt t -
      linearMixed E pr t ^ 2 = (w * wr / r) / D ^ 2) ∧
  (∀ r E Er k p kr pr pt t : ℝ,
    scaledCoordinateResidual r E Er k p kr pr pt t = 0 →
    correctedAngular r E Er k p kr pr pt t = linearAngular r E Er k kr t) ∧
  (∀ r w wr : ℝ,
    heightDiscriminant (radialEnergy w) w 0 = 1 ∧
    linearRadial (radialEnergy w) w 0 1 = w ∧
    linearMixed (radialEnergy w) 0 1 = 0 ∧
    linearAngular r (radialEnergy w) (2 * w * wr) w wr 1 = wr / r)

/-- The entire pointwise S03 conclusion, rather than an independent jet
identity or a predicate arbitrarily called flatness. -/
def ScalarCoreAt (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : Prop :=
  x.1 * radialPartial (heightAngular z) x =
      angularPartial (heightRadial z) x - heightAngular z x ∧
  exteriorCoefficient (heightCoframeOne w z) x =
      wedgeCoefficient (heightConnectionForm w z) (heightCoframeTwo w z) x ∧
  exteriorCoefficient (heightCoframeTwo w z) x =
      -wedgeCoefficient (heightConnectionForm w z) (heightCoframeOne w z) x ∧
  (heightConnectionForm w z).radial x =
    heightRadial z x * radialPartial (heightAngular z) x /
      ((1 - heightAngular z x ^ 2) * Real.sqrt (polarDiscriminant w z x)) ∧
  (heightConnectionForm w z).angular x =
    (1 + heightRadial z x * angularPartial (heightAngular z) x /
      (1 - heightAngular z x ^ 2)) / Real.sqrt (polarDiscriminant w z x) ∧
  exteriorCoefficient (heightConnectionForm w z) x = x.1 * polarCoordinateResidual w z x ∧
  ∀ η : PolarPoint → ℝ, ContDiff ℝ ∞ η →
    HasDerivAt (fun t => x.1 * polarCoordinateResidual w (heightFamily z η t) x)
      (heightLinearizedDivergence w z η x) 0

/-- S03, `prop:scalar-core`: actual scalar calculus and actual local
Euclidean development on convex open coordinate neighborhoods. -/
def S03CalculusStatement : Prop :=
  (∀ (w : ℝ → ℝ) (z : PolarPoint → ℝ), ContDiff ℝ ∞ w → ContDiff ℝ ∞ z →
    ∀ x : PolarPoint, 0 < x.1 → 0 < polarDiscriminant w z x → ScalarCoreAt w z x) ∧
  (∀ (U : Set PolarPoint) (w : ℝ → ℝ) (z : PolarPoint → ℝ),
    IsOpen U → Convex ℝ U → ContDiff ℝ ∞ w → ContDiff ℝ ∞ z →
    (∀ x ∈ U, 0 < x.1 ∧ 0 < polarDiscriminant w z x ∧
      polarCoordinateResidual w z x = 0) →
    ∃ P : PolarPoint → PolarPoint,
      (∀ x ∈ U, ContDiffAt ℝ ∞ P x) ∧
      (∀ x ∈ U, ∀ u v : PolarPoint,
        coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) =
          remainderBilinear x.1 (profileEnergy w x) (heightRadial z x)
            (heightAngular z x) u v) ∧
      ∀ x ∈ U, ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
        (e : PolarPoint → PolarPoint) = P ∧ x ∈ e.source ∧
          P x ∈ e.target ∧ ContDiffAt ℝ ∞ e.symm (P x))

/-- The actual removable normalized residual, using the actual radial
primitive `h`, not a freely chosen residual map. -/
def normalizedResidual (w h : ℝ → ℝ) (u : PolarPoint → ℝ) (q : ℝ)
    (x : PolarPoint) : ℝ :=
  normalizedHeightResidual w (Radial.radialHeightField h) u q x

/-- Physical normalized angular mean: the source is `dr dθ`. -/
def normalizedSourceIntegral (w h : ℝ → ℝ) (u : PolarPoint → ℝ)
    (q a b : ℝ) : ℝ :=
  ∫ r in a..b, (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), normalizedResidual w h u q (r, θ)

/-- Actual endpoint jets suffice for the finite-annulus conservation
statement. The two endpoint height values are not identified. -/
def AdmissibleScalarData (a b : ℝ) (w h : ℝ → ℝ)
    (u : PolarPoint → ℝ) (q : ℝ) : Prop :=
  0 < a ∧ a < b ∧ ContDiff ℝ ∞ w ∧ ContDiff ℝ ∞ h ∧ ContDiff ℝ ∞ u ∧
  (∀ r, HasDerivAt h (w r) r) ∧
  Function.Periodic u (0, 2 * Real.pi) ∧
  w a = 0 ∧ w b = 0 ∧
  (∀ θ, heightRadial u (a, θ) = 0 ∧ heightAngular u (a, θ) = 0 ∧
    heightRadial u (b, θ) = 0 ∧ heightAngular u (b, θ) = 0) ∧
  ∀ r ∈ Icc a b, ∀ θ,
    0 < polarDiscriminant w (heightFamily (Radial.radialHeightField h) u q) (r, θ)

/-- S04, `eq:normalized-integral` and `eq:zero-total-integral`.
The last clause explicitly includes metric/height mixed parameter
derivatives on every finite-dimensional parameter family. -/
def S04CalculusStatement : Prop :=
  (∀ (w h : ℝ → ℝ) (u : PolarPoint → ℝ), ContDiff ℝ ∞ w →
    ContDiff ℝ ∞ h → ContDiff ℝ ∞ u → (∀ r, HasDerivAt h (w r) r) →
    ∀ (q : ℝ) (x : PolarPoint), 0 < x.1 →
    (∀ t ∈ Icc (0 : ℝ) 1,
      0 < polarDiscriminant w (heightFamily (Radial.radialHeightField h) u (t * q)) x) →
    normalizedResidual w h u q x =
      ∫ t in (0 : ℝ)..1,
        heightLinearizedDivergence w (heightFamily (Radial.radialHeightField h) u (t * q)) u x) ∧
  (∀ (w h : ℝ → ℝ) (u : PolarPoint → ℝ), ContDiff ℝ ∞ w →
    ContDiff ℝ ∞ h → ContDiff ℝ ∞ u → (∀ r, HasDerivAt h (w r) r) →
    ∀ x : PolarPoint, 0 < x.1 →
      ContDiffAt ℝ ∞ (fun q => normalizedResidual w h u q x) 0 ∧
      normalizedResidual w h u 0 x = Radial.radialPDE w (fun r θ => u (r, θ)) x.1 x.2) ∧
  (∀ (a b q : ℝ) (w h : ℝ → ℝ) (u : PolarPoint → ℝ),
    AdmissibleScalarData a b w h u q → normalizedSourceIntegral w h u q a b = 0 ∧
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (heightConnectionForm w (heightFamily (Radial.radialHeightField h) u q)).angular (a, θ)) =
        2 * Real.pi ∧
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (heightConnectionForm w (heightFamily (Radial.radialHeightField h) u q)).angular (b, θ)) =
        2 * Real.pi) ∧
  (∀ (n : ℕ) (W H : (Fin n → ℝ) × ℝ → ℝ)
    (U : (Fin n → ℝ) × PolarPoint → ℝ),
    ContDiff ℝ ∞ W → ContDiff ℝ ∞ H → ContDiff ℝ ∞ U →
    (∀ p r, HasDerivAt (fun s => H (p, s)) (W (p, r)) r) →
    ∀ (p : Fin n → ℝ) (q : ℝ) (x : PolarPoint), 0 < x.1 →
    0 < polarDiscriminant (fun r => W (p, r))
      (heightFamily (Radial.radialHeightField (fun r => H (p, r))) (fun y => U (p, y)) q) x →
    ContDiffAt ℝ ∞ (fun s : (Fin n → ℝ) × ℝ × PolarPoint =>
      normalizedResidual (fun r => W (s.1, r)) (fun r => H (s.1, r))
        (fun y => U (s.1, y)) s.2.1 s.2.2) (p, q, x)) ∧
  (∀ (n : ℕ) (W H : (Fin n → ℝ) × ℝ → ℝ)
    (U : (Fin n → ℝ) × PolarPoint → ℝ) (q : (Fin n → ℝ) → ℝ)
    (O : Set (Fin n → ℝ)) (a b : ℝ), IsOpen O →
    ContDiff ℝ ∞ W → ContDiff ℝ ∞ H → ContDiff ℝ ∞ U → ContDiff ℝ ∞ q →
    (∀ p ∈ O, AdmissibleScalarData a b (fun r => W (p, r)) (fun r => H (p, r))
      (fun x => U (p, x)) (q p)) →
    ∀ p ∈ O, ∀ s : ℕ,
      iteratedFDeriv ℝ s (fun p => normalizedSourceIntegral
        (fun r => W (p, r)) (fun r => H (p, r)) (fun x => U (p, x)) (q p) a b) p = 0 ∧
      ∀ directions : Fin s → (Fin n → ℝ),
        (∫ r in a..b, (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (iteratedFDeriv ℝ s (fun p => normalizedResidual
            (fun r => W (p, r)) (fun r => H (p, r)) (fun x => U (p, x))
              (q p) (r, θ)) p) directions) = 0)

/-- The explicit angular divergence error on *independent* residual and
increment variables. It does not name an arbitrary bilinear map. -/
def scalarCorrectionError (B R η : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  angularPartial (fun y => B y * R y * angularPartial η y) x

def characteristicDrift (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  profileEnergy w x * (heightAngular z x - angularPartial (heightRadial z) x) /
    (x.1 * heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x))

def characteristicSpeed (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  Real.sqrt (-w x.1 * deriv w x.1 / x.1) * Real.sqrt (polarDiscriminant w z x) /
    heightQ (profileEnergy w x) (heightRadial z x) (angularPartial (heightAngular z) x)

def correctedCharacteristicEquation (w : ℝ → ℝ) (z : PolarPoint → ℝ)
    (x : PolarPoint) (s : ℝ) : Prop :=
  polarLinearA w z x * s ^ 2 - 2 * polarLinearB w z x * s + polarCorrectedC w z x = 0

/-- A concrete symmetric scalar divergence operator and its physical
radial conormal flux. Changing its `c` field does not redefine the flux. -/
structure ScalarDivergenceOperator where
  a : PolarPoint → ℝ
  b : PolarPoint → ℝ
  c : PolarPoint → ℝ

def ScalarDivergenceOperator.apply (L : ScalarDivergenceOperator)
    (u : PolarPoint → ℝ) : PolarPoint → ℝ := symmetricDivergence L.a L.b L.c u

def ScalarDivergenceOperator.normalFlux (L : ScalarDivergenceOperator)
    (u : PolarPoint → ℝ) : PolarPoint → ℝ := symmetricNormalFlux L.a L.b u

def trueHeightOperator (w : ℝ → ℝ) (z : PolarPoint → ℝ) : ScalarDivergenceOperator :=
  ⟨polarLinearA w z, polarLinearB w z, polarLinearC w z⟩

def correctedHeightOperator (w : ℝ → ℝ) (z : PolarPoint → ℝ) : ScalarDivergenceOperator :=
  ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩

/-- S05, `lem:type-completion`, including the actual state derivative of
the normalized residual (also at q=0), independent-variable error,
physical Green pairing, and the simple-turning-point square-root germ. -/
def S05CalculusStatement : Prop :=
  (∀ (w h : ℝ → ℝ) (u η : PolarPoint → ℝ),
    ContDiff ℝ ∞ w → ContDiff ℝ ∞ h → ContDiff ℝ ∞ u → ContDiff ℝ ∞ η →
    (∀ r, HasDerivAt h (w r) r) →
    ∀ (q : ℝ) (x : PolarPoint), 0 < x.1 → 0 < w x.1 →
    let z := heightFamily (Radial.radialHeightField h) u q
    (1 / 2 : ℝ) ≤ polarDiscriminant w z x →
    (7 / 8 : ℝ) * w x.1 ≤ heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x) →
    HasDerivAt (fun t => normalizedResidual w h (heightFamily u η t) q x)
      (heightCorrectedDivergence w z η x + q *
        scalarCorrectionError (polarTypeB w z) (normalizedResidual w h u q) η x) 0 ∧
    polarLinearA w z x * polarCorrectedC w z x - polarLinearB w z x ^ 2 =
      (w x.1 * deriv w x.1 / x.1) / polarDiscriminant w z x ^ 2) ∧
  (∀ (w : ℝ → ℝ) (z η : PolarPoint → ℝ),
    (trueHeightOperator w z).normalFlux η = (correctedHeightOperator w z).normalFlux η) ∧
  (∀ (w : ℝ → ℝ) (z : PolarPoint → ℝ) (c : ℝ) (x : PolarPoint),
    heightCorrectedDivergence w z (fun _ => c) x = 0) ∧
  (∀ (B R S η ξ : PolarPoint → ℝ),
    ContDiff ℝ ∞ B → ContDiff ℝ ∞ R → ContDiff ℝ ∞ S →
    ContDiff ℝ ∞ η → ContDiff ℝ ∞ ξ → ∀ (c : ℝ) (x : PolarPoint),
    scalarCorrectionError B (fun y => R y + S y) η x =
      scalarCorrectionError B R η x + scalarCorrectionError B S η x ∧
    scalarCorrectionError B R (fun y => η y + ξ y) x =
      scalarCorrectionError B R η x + scalarCorrectionError B R ξ x ∧
    scalarCorrectionError B (fun y => c * R y) η x = c * scalarCorrectionError B R η x ∧
    scalarCorrectionError B R (fun y => c * η y) x = c * scalarCorrectionError B R η x) ∧
  (∀ (B R η : PolarPoint → ℝ),
    ContDiff ℝ ∞ B → ContDiff ℝ ∞ R → ContDiff ℝ ∞ η →
    Function.Periodic B (0, 2 * Real.pi) → Function.Periodic R (0, 2 * Real.pi) →
    Function.Periodic η (0, 2 * Real.pi) → ∀ a b : ℝ,
      (∫ r in a..b, (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        scalarCorrectionError B R η (r, θ)) = 0) ∧
  (∀ (w : ℝ → ℝ) (z φ ψ : PolarPoint → ℝ) (a b : ℝ),
    0 < a → a < b → ContDiff ℝ ∞ w → ContDiff ℝ ∞ z →
    ContDiff ℝ ∞ φ → ContDiff ℝ ∞ ψ →
    Function.Periodic z (0, 2 * Real.pi) → Function.Periodic φ (0, 2 * Real.pi) →
    Function.Periodic ψ (0, 2 * Real.pi) →
    (∀ x ∈ Icc a b ×ˢ Icc (0 : ℝ) (2 * Real.pi),
      0 < polarDiscriminant w z x ∧
      heightQ (profileEnergy w x) (heightRadial z x) (angularPartial (heightAngular z) x) ≠ 0) →
    (∀ θ, greenNormalFlux (polarLinearA w z) (polarLinearB w z) φ ψ (a, θ) = 0 ∧
      greenNormalFlux (polarLinearA w z) (polarLinearB w z) φ ψ (b, θ) = 0) →
    (∫ r in a..b, ∫ θ in (0 : ℝ)..(2 * Real.pi),
      φ (r, θ) * heightCorrectedDivergence w z ψ (r, θ) -
        ψ (r, θ) * heightCorrectedDivergence w z φ (r, θ)) = 0) ∧
  (∀ (w : ℝ → ℝ) (z : PolarPoint → ℝ), ContDiff ℝ ∞ w → ContDiff ℝ ∞ z →
    ∀ x : PolarPoint, 0 < x.1 → 0 < w x.1 → deriv w x.1 < 0 →
    0 < polarDiscriminant w z x →
    0 < heightQ (profileEnergy w x) (heightRadial z x) (angularPartial (heightAngular z) x) →
    ∀ s : ℝ, correctedCharacteristicEquation w z x s ↔
      s = characteristicDrift w z x - characteristicSpeed w z x ∨
      s = characteristicDrift w z x + characteristicSpeed w z x) ∧
  (∀ (w : ℝ → ℝ) (z : PolarPoint → ℝ), ContDiff ℝ ∞ w → ContDiff ℝ ∞ z →
    ∀ r θ σ : ℝ, 0 < r → 0 < w r → deriv w r = 0 →
    σ ^ 2 = 1 → σ * deriv (deriv w) r < 0 →
    0 < polarDiscriminant w z (r, θ) →
    0 < heightQ (profileEnergy w (r, θ)) (heightRadial z (r, θ))
      (angularPartial (heightAngular z) (r, θ)) →
    ∃ (δ : ℝ) (factor : PolarPoint → ℝ), 0 < δ ∧
      ContDiffAt ℝ ∞ factor (0, θ) ∧
      (∀ t ∈ Icc (0 : ℝ) δ, ∀ φ ∈ Ioo (θ - δ) (θ + δ), 0 < factor (t, φ)) ∧
      ∀ t ∈ Ioo (0 : ℝ) δ, ∀ φ ∈ Ioo (θ - δ) (θ + δ),
        characteristicSpeed w z (r + σ * t, φ) = Real.sqrt t * factor (t, φ))

end ContinuousFlexibility.Statements
