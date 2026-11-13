import ContinuousFlexibility.Analysis.N04SourceColumnsData
import ContinuousFlexibility.Analysis.AngularSimpleDivisionBounds

/-!
# Spatial differentiation of scalar current-jet data

Taking `r` radial and `t` angular derivatives costs exactly `r+t` in the
fixed loss. The parameter neighborhood and its low seminorm are unchanged.
The witness differentiates the actual current-minus-reference field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

theorem n04SourceColumns_mixedDerivative_periodic
    {f : PolarPoint → ℝ}
    (hf : ∀ q ∈ unitStrip, f (q + (0, Real.pi)) = f q) (r t : ℕ) :
    ∀ q ∈ unitStrip,
      mixedDerivative r t f (q + (0, Real.pi)) = mixedDerivative r t f q := by
  have he : EqOn (fun p : PolarPoint => f (p.1, p.2 + Real.pi)) f unitStrip := by
    intro q hq
    simpa only [Prod.mk_add_mk, add_zero] using hf q hq
  intro q hq
  have h := n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ) he r t hq
  rw [mixedDerivative_angularTranslate] at h
  simpa only [Prod.mk_add_mk, add_zero] using h

variable {T : MaterialData} {cell : ℕ → ℕ}

/-- Spatial jets of a reference family have the same kind of coefficient
envelope, with the order shifted before choosing the constant. -/
theorem N04SourceReferenceData.sourceColumns_mixedDerivative
    {f₀ : ℕ → PolarPoint → ℝ} (h₀ : N04SourceReferenceData T cell f₀) (r t : ℕ) :
    N04SourceReferenceData T cell (fun m => mixedDerivative r t (f₀ m)) := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  refine ⟨fun m => ⟨contDiffOn_mixedDerivative hU (h₀.1 m).1 r t,
    n04SourceColumns_mixedDerivative_periodic (h₀.1 m).2 r t⟩, fun s => ?_⟩
  have hb := h₀.2 (s + r + t)
  refine ⟨hb.choose, hb.choose_spec.1, fun m q hq i j hij => ?_⟩
  rw [n07a_mixedDerivative_mixedDerivative_on hU (h₀.1 m).1 i j r t hq]
  exact hb.choose_spec.2 m q hq (i + r) (j + t) (by omega)

variable {S : PhysicalSpacesData} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Differentiation preserves current data and its genuine parameter
tower; the total spatial order is absorbed into the fixed loss. -/
theorem CurrentJetDataOn.sourceColumns_mixedDerivative
    (h : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (h₀ : N04SourceReferenceData T cell f₀) (r t : ℕ) :
    CurrentJetDataOn S T cell (fun _ => True) base ε
      (fun z m => mixedDerivative r t (f z m))
      (fun m => mixedDerivative r t (f₀ m)) := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have he (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m i j : ℕ) (q : unitStrip) :
      mixedDerivative i j
          (fun y => mixedDerivative r t (f z m) y - mixedDerivative r t (f₀ m) y) q.val =
        mixedDerivative (i + r) (j + t) (fun y => f z m y - f₀ m y) q.val := by
    rw [mixedDerivative_sub_of_contDiffOn hU
      (contDiffOn_mixedDerivative hU (h.1 z hz m trivial).1 r t)
      (contDiffOn_mixedDerivative hU (h₀.1 m).1 r t) i j q.property,
      n07a_mixedDerivative_mixedDerivative_on hU (h.1 z hz m trivial).1 i j r t q.property,
      n07a_mixedDerivative_mixedDerivative_on hU (h₀.1 m).1 i j r t q.property,
      mixedDerivative_sub_of_contDiffOn hU (h.1 z hz m trivial).1 (h₀.1 m).1
        (i + r) (j + t) q.property]
  let J : ∀ m (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j
          (fun y => mixedDerivative r t (f z m) y - mixedDerivative r t (f₀ m) y) q.val) :=
    fun m i j q => (h.2.choose m (i + r) (j + t) q).congrOn
      (fun z hz => (he z hz m i j q).symm)
  refine ⟨fun z hz m _ =>
    ⟨contDiffOn_mixedDerivative hU (h.1 z hz m trivial).1 r t,
      n04SourceColumns_mixedDerivative_periodic (h.1 z hz m trivial).2 r t⟩,
    J, ?_, ?_⟩
  · have hv := h.2.choose_spec.1
    refine ⟨r + t + hv.choose, fun s => ?_⟩
    have hb := hv.choose_spec (s + r + t)
    refine ⟨hb.choose, hb.choose_spec.1, fun z hz m _ q i j hij => ?_⟩
    rw [he z hz m i j q]
    have hb' := hb.choose_spec.2 z hz m trivial q (i + r) (j + t) (by omega)
    simpa only [Nat.add_assoc] using hb'
  · intro k
    have ht := h.2.choose_spec.2 k
    refine ⟨r + t + ht.choose, fun s => ?_⟩
    have hb := ht.choose_spec (s + r + t)
    refine ⟨hb.choose, hb.choose_spec.1, fun z hz v m _ q i j hij => ?_⟩
    change |(h.2.choose m (i + r) (j + t) q).D k z v| ≤ _
    have hb' := hb.choose_spec.2 z hz v m trivial q (i + r) (j + t) (by omega)
    simpa only [Nat.add_assoc] using hb'

end ContinuousFlexibility.Analysis
