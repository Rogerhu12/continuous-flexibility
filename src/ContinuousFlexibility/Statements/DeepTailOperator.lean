module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The deep-tail operator statement layer

The scalar density, weighted Hilbert space and Friedrichs form definitions
are independent of the oscillator, the reference surface and physical-radius
matching. They retain the original declaration names and definitions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory Real
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace BigOperators

structure DeepTailData where
  entrance : ℝ
  endpoint : ℝ
  p : ℝ → ℝ
  node : ℕ → ℝ
  massEnd : ℕ → ℝ
  Λ : ℝ
  η : ℝ
  K : ℝ

def deepTailMeasure (T : DeepTailData) : Measure ℝ :=
  (volume.restrict (Ioo T.entrance T.endpoint)).withDensity (fun x => ENNReal.ofReal (T.p x))

abbrev DeepTailL2 (T : DeepTailData) := MeasureTheory.Lp ℝ 2 (deepTailMeasure T)

def tailMass (T : DeepTailData) (n : ℕ) : ℝ :=
  ∫ x in T.node n..T.massEnd n, T.p x
def tailInnerResistance (T : DeepTailData) (n : ℕ) : ℝ :=
  ∫ x in T.node n..T.massEnd n, (T.p x)⁻¹
def tailGapMass (T : DeepTailData) (n : ℕ) : ℝ :=
  ∫ x in T.massEnd n..T.node (n + 1), T.p x
def tailResistance (T : DeepTailData) (n : ℕ) : ℝ :=
  ∫ x in T.massEnd n..T.node (n + 1), (T.p x)⁻¹

def tailInitialGapMass (T : DeepTailData) : ℝ :=
  ∫ x in T.entrance..T.node 0, T.p x

def tailInitialResistance (T : DeepTailData) : ℝ :=
  ∫ x in T.entrance..T.node 0, (T.p x)⁻¹

/-- Nodes index outward mass intervals.  A left tail may have a separate
initial resistance edge, and its edge following I_n is the original J_(n+1). -/
def DeepTailHypotheses (T : DeepTailData) : Prop :=
  T.entrance < T.endpoint ∧ T.entrance ≤ T.node 0 ∧ 0 < T.Λ ∧
    (T.node 0 = T.entrance ∨
      (T.entrance < T.node 0 ∧
        T.Λ * tailInitialGapMass T * tailInitialResistance T ≤ T.η ∧
        tailInitialGapMass T ≤ T.η * tailMass T 0 ∧
        T.K ≤ T.Λ * tailMass T 0 * tailInitialResistance T)) ∧
    0 < T.η ∧ T.η < 1 ∧ 1 < T.K ∧
    ContDiffOn ℝ ∞ T.p (Ico T.entrance T.endpoint) ∧
    (∀ x ∈ Ico T.entrance T.endpoint, 0 < T.p x) ∧
    Tendsto T.node atTop (𝓝 T.endpoint) ∧
    (∀ n, T.node n < T.massEnd n ∧ T.massEnd n < T.node (n + 1) ∧
      T.Λ * tailMass T n * tailInnerResistance T n +
        T.Λ * tailGapMass T n * tailResistance T n ≤ T.η ∧
      T.K ≤ T.Λ * tailMass T n * tailResistance T n ∧
      T.K ≤ T.Λ * tailMass T (n + 1) * tailResistance T n ∧
      tailGapMass T n ≤ T.η * min (tailMass T n) (tailMass T (n + 1)))

def TailEnergyCore (T : DeepTailData) (endCut : ℝ) :
    Set (DeepTailL2 T × DeepTailL2 T) :=
  {p | ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ioo T.entrance endCut ∧
    (p.1 : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ ∧
    (p.2 : ℝ → ℝ) =ᵐ[deepTailMeasure T] deriv φ}

/-- The Friedrichs form domain is the energy-norm closure of compact tests. -/
def TailFormLift (T : DeepTailData) (endCut : ℝ) :
    Set (DeepTailL2 T × DeepTailL2 T) := closure (TailEnergyCore T endCut)

def TailFriedrichsGraph (T : DeepTailData) (endCut : ℝ)
    (u f : DeepTailL2 T) : Prop :=
  ∃ du : DeepTailL2 T, (u, du) ∈ TailFormLift T endCut ∧
    ∀ p ∈ TailFormLift T endCut, ⟪f, p.1⟫_ℝ = ⟪du, p.2⟫_ℝ

def TailWeakDerivative (T : DeepTailData) (endCut : ℝ)
    (u d : DeepTailL2 T) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Ioo T.entrance endCut →
    (∫ x : ℝ, u x * deriv ψ x) = -(∫ x : ℝ, d x * ψ x)

def TailDistributionGraph (T : DeepTailData) (endCut : ℝ)
    (u f : DeepTailL2 T) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Ioo T.entrance endCut →
    (∫ x, f x * ψ x ∂deepTailMeasure T) =
      ∫ x, u x * (-(T.p x)⁻¹ * deriv (fun y => T.p y * deriv ψ y) x) ∂deepTailMeasure T

def TailFormIdentification (T : DeepTailData) (endCut : ℝ) : Prop :=
  (∀ u d, (u, d) ∈ TailFormLift T endCut → TailWeakDerivative T endCut u d) ∧
  (∀ d, (0, d) ∈ TailFormLift T endCut → d = 0) ∧
  (∀ u f, TailFriedrichsGraph T endCut u f ↔
    (∃ d, (u, d) ∈ TailFormLift T endCut) ∧ TailDistributionGraph T endCut u f)

def TailNaturalEquation (T : DeepTailData) (u : ℝ → ℝ) : Prop :=
  ContDiffAt ℝ ∞ u T.entrance ∧ ContDiffOn ℝ ∞ u (Ioo T.entrance T.endpoint) ∧
    MemLp u 2 (deepTailMeasure T) ∧
    ∀ x ∈ Ioo T.entrance T.endpoint,
      deriv (fun y => T.p y * deriv u y) x + T.Λ * T.p x * u x = 0

def TailNaturalLineAndKernel (T : DeepTailData) : Prop :=
  ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧
    (∃ x ∈ Ioo T.entrance T.endpoint, u x ≠ 0) ∧
    (∀ v, TailNaturalEquation T v → ∃ c : ℝ,
      ∀ x ∈ Ioo T.entrance T.endpoint, v x = c * u x) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |u (T.node (n + 1))| ≤ C /
        (T.Λ * tailMass T (n + 1) * tailResistance T n) * |u (T.node n)|)

def TailGreenKernel (T : DeepTailData)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T) : Prop :=
  ∃ κ : ℝ → ℝ → ℝ,
    Measurable (fun z : ℝ × ℝ => κ z.1 z.2) ∧
    (∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ Ioo T.entrance T.endpoint →
      ∀ᵐ x ∂deepTailMeasure T, Integrable (fun y => κ x y * ψ y) (deepTailMeasure T)) ∧
    (∀ f : DeepTailL2 T, ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ Ioo T.entrance T.endpoint →
      ((f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ) →
      ((G f : DeepTailL2 T) : ℝ → ℝ) =ᵐ[deepTailMeasure T]
        (fun x => ∫ y, κ x y * ψ y ∂deepTailMeasure T)) ∧
    (∀ x y, κ x y = κ y x) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, m ≤ n →
      ∀ x ∈ Ioo (T.node m) (T.node (m + 1)),
      ∀ y ∈ Ioo (T.node n) (T.node (n + 1)),
        |κ x y| ≤ C *
          (1 + tailInnerResistance T m + tailResistance T m + (T.Λ * tailMass T m)⁻¹) *
          (1 + tailInnerResistance T n + tailResistance T n + (T.Λ * tailMass T n)⁻¹) *
          ∏ k ∈ Finset.Ico m n, C /
            (T.Λ * tailMass T (k + 1) * tailResistance T k))

end ContinuousFlexibility.Statements
