module

public import ContinuousFlexibility.Analysis.N06DegenerateGraph
public import ContinuousFlexibility.Analysis.N06RelativeConstruction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The analytic substatements of N06

The modal statement concerns the actual maximal distributional graph with L²
forcing and no prescribed endpoint values. The canonical statement constructs
the physical operator on one chosen N05 source and graph, with a uniform
linear displacement bound. Neither substatement assumes a small relative
operator or a Neumann inverse. The latter are assembled after the neighborhood
has been restricted once.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The positive-cylinder estimate on the actual weak modal graph. -/
def N06WeakGraphStatement : Prop :=
  ∀ a c V q u F : ℝ → ℝ, ∀ j K : ℝ,
    ContDiff ℝ ∞ a → Continuous c → Continuous V → ContDiff ℝ 2 q →
    MemLp u 2 (volume.restrict (Ioo (0 : ℝ) 1)) →
    MemLp F 2 (volume.restrict (Ioo (0 : ℝ) 1)) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 →
        (∫ y in (0 : ℝ)..1, u y * (-deriv (fun t => a t * deriv φ t) y +
          (j ^ 2 * c y + V y) * φ y)) = ∫ y in (0 : ℝ)..1, F y * φ y) →
    1 ≤ K →
    (∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y) →
    (∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K) →
    (∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K) →
    (∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y) →
    (∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K) →
    (∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y) →
    (∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) →
    ∃ v : ℝ → ℝ,
      u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v ∧
      ContDiff ℝ 1 v ∧ AbsolutelyContinuousOnInterval (deriv v) 0 1 ∧
      MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      MemLp (deriv v) 2 (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      (∀ᵐ y ∂volume.restrict (Ioo (0 : ℝ) 1),
        -deriv (fun t => a t * deriv v t) y +
          j ^ 2 * c y * v y + V y * v y = F y) ∧
      (∫ y in (0 : ℝ)..1, (cylinderWeight y * deriv v y) ^ 2) +
        (1 + j ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 3 * v y ^ 2) +
        (∫ y in (0 : ℝ)..1, (cylinderWeight y ^ 2 * deriv (deriv v) y) ^ 2) +
        (1 + j ^ 2) ^ 2 * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 6 * v y ^ 2) +
        (1 + j ^ 2) * (∫ y in (0 : ℝ)..1, cylinderWeight y ^ 5 * deriv v y ^ 2) ≤
        16384 * K ^ 10 * ((∫ y in (0 : ℝ)..1, F y ^ 2) +
          ∫ y in (0 : ℝ)..1, u y ^ 2)

/-- The actual current physical operator and its uniform relative estimate,
retaining every N05 property on the same selected construction. The canonical
witness must be constructed with the required geometry; no regularity or
smallness of an arbitrary N04 witness is silently assumed. -/
def N06CanonicalRelativeStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ V : VolumeModelData S K, ∃ b : ℕ,
          ∃ B : CanonicalDomainData S K V b,
            ∃ base loss : ℕ, ∃ ε : ℝ,
              IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
                NonlinearPropertiesThrough05 A.val T S C R L K V b B base loss ε ∧
                ∃ P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
                  ∃ order : ℕ, ∃ M : ℝ, 0 ≤ M ∧
                    (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
                      ∀ u : B.Space, PerturbedCanonicalRelation A.val S C K L z u.val.1
                        (V.forget (3 / 4 : ℝ) 0 b (P z u))) ∧
                    (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
                      ‖n06RelativeOperator P z‖ ≤
                        M * (stateGrading S order (z.1 - C.referenceState) + |z.2|))

end ContinuousFlexibility.Statements
