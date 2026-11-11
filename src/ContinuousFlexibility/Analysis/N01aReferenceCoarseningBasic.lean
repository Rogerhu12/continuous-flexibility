import ContinuousFlexibility.Analysis.N01aCellCoarseningSeries
import ContinuousFlexibility.Analysis.N01aReferencePartitionSquares

/-!
# Coarsening a reference partition without changing its physical fields

The relation records only the actual finite-fiber sum and the unchanged
physical data. Geometric construction of the grouped cells is separate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators

structure N01aReferenceCoarsening (D E : ReferenceData) (σ : ℕ → ℕ) : Prop where
  finite_fibers : ∀ j, {i | σ i = j}.Finite
  a_eq : E.a = D.a
  b_eq : E.b = D.b
  w_eq : E.w = D.w
  phi_eq : E.phi = D.phi
  chi_eq : E.chi = D.chi
  chiLeft_eq : E.chiLeft = D.chiLeft
  index_eq : ∀ i, E.cellIndex (σ i) = D.cellIndex i
  localizer_eq : ∀ j r, E.localizer j r =
    ∑ i ∈ n01aCoarseningFiber σ finite_fibers j, D.localizer i r

namespace N01aReferenceCoarsening

variable {D E : ReferenceData} {σ : ℕ → ℕ} (h : N01aReferenceCoarsening D E σ)

include h

theorem core_eq : radialCore E = radialCore D := by
  simp only [radialCore, h.a_eq, h.b_eq]

theorem measure_eq : radialPhysicalMeasure E = radialPhysicalMeasure D := by
  simp only [radialPhysicalMeasure, h.core_eq]

theorem column_eq : referenceColumn E = referenceColumn D := by
  simp only [referenceColumn, h.w_eq, h.phi_eq, h.chi_eq]

theorem row_eq (u : PolarPoint → ℝ) : referenceRow E u = referenceRow D u := by
  simp only [referenceRow, h.a_eq, h.b_eq, h.column_eq]

theorem remainder_eq (aL : ℝ) (U : RadialUnknown) :
    outputRemainder E aL U = outputRemainder D aL U := by
  simp only [outputRemainder, h.chiLeft_eq]

theorem test_iff (ψ : PolarPoint → ℝ) : RadialTest E ψ ↔ RadialTest D ψ := by
  simp only [RadialTest, h.core_eq]

theorem weakPairing_eq (u ψ : PolarPoint → ℝ) :
    radialWeakPairing E u ψ = radialWeakPairing D u ψ := by
  simp only [radialWeakPairing, h.a_eq, h.b_eq, h.w_eq]

theorem representative_iff (U V : RadialUnknown) :
    RadialRepresentativeEq E U V ↔ RadialRepresentativeEq D U V := by
  simp only [RadialRepresentativeEq, h.measure_eq]

theorem smooth_iff (U : RadialUnknown) :
    SmoothAdmissibleField E U ↔ SmoothAdmissibleField D U := by
  simp only [SmoothAdmissibleField, h.a_eq, h.b_eq]

theorem normal_iff (u d : PolarPoint → ℝ) :
    WeakNormalDerivative E u d ↔ WeakNormalDerivative D u d := by
  simp only [WeakNormalDerivative, h.test_iff, h.a_eq, h.b_eq]

theorem angular_iff (u d : PolarPoint → ℝ) :
    WeakAngularDerivative E u d ↔ WeakAngularDerivative D u d := by
  simp only [WeakAngularDerivative, h.test_iff, h.a_eq, h.b_eq]

theorem coarse_localizer_apply (j : ℕ) (p : PolarPoint) :
    n01aCoarseLocalizer σ h.finite_fibers (fun i (p : PolarPoint) => D.localizer i p.1)
      j p = E.localizer j p.1 := (h.localizer_eq j p.1).symm

theorem cell_integrable_iff (hD : RadialPartition D) (hE : RadialPartition E)
    (f : PolarPoint → ℝ) : RadialCellIntegrable E f ↔ RadialCellIntegrable D f := by
  have hm (i : ℕ) : AEMeasurable (fun p : PolarPoint => D.localizer i p.1)
      (radialPhysicalMeasure D) :=
    ((hD.1 i).continuous.comp continuous_fst).measurable.aemeasurable
  have hn (i : ℕ) (p : PolarPoint) : 0 ≤ D.localizer i p.1 := hD.2.1 i p.1
  constructor
  · intro hf
    have hfm : AEMeasurable (fun p => f p ^ 2) (radialPhysicalMeasure D) := by
      simpa only [h.measure_eq] using hf.aemeasurable_sq hE
    have hc : ∀ j, Integrable
        (fun p => (n01aCoarseLocalizer σ h.finite_fibers
          (fun i (p : PolarPoint) => D.localizer i p.1) j p * f p) ^ 2)
        (radialPhysicalMeasure D) := by
      intro j
      simpa only [h.coarse_localizer_apply, h.measure_eq] using hf.integrable_square j
    exact (n01aCoarseLocalizer_integrable_iff (radialPhysicalMeasure D) σ h.finite_fibers
      hn hm hfm).mp hc
  · intro hf
    intro j
    have hc := n01aCoarseLocalizer_square_integrable (radialPhysicalMeasure D)
      σ h.finite_fibers hm (hf.aemeasurable_sq hD) (fun i => hf.integrable_square i) j
    simpa only [h.coarse_localizer_apply, ← h.measure_eq] using hc

end N01aReferenceCoarsening

end ContinuousFlexibility.Statements
