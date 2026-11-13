import ContinuousFlexibility.Analysis.N04PulledFieldsRawPrefix
import ContinuousFlexibility.Analysis.N04PulledFieldsInverseRawBounds

/-!
# Common raw losses for a finite family of geometry atoms

The concrete current-data adapters supply the original scalar bounds.
Finite sums, zero-order identities and interpolation are handled over
an abstract parameter space in `N04PulledFieldsInverseRawBounds`.
The public interfaces retain the exact supplied mixed and joint towers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

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

private theorem n04PulledFieldsInverseRawFamily_zero_input
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m (q : unitStrip) (a b : ℕ),
      a + b ≤ s → |mixedDerivative a b (f₀ m) q.val| ≤ B * T.E0 (T.sample (cell m)) ^ B) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ sectorNeighborhood S base ε ε, ∀ m (q : unitStrip) (a b : ℕ), a + b ≤ s →
        |mixedDerivative a b (f x m) q.val| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          (1 + T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) * parameterGrading S (s + d) x) := by
  let data := n04PulledFields_currentData_rawSpatial hdata hE hH (fun m _ => hreg m)
    (fun s => ⟨(href s).choose, (href s).choose_spec.1,
      fun m _ q a b hab => (href s).choose_spec.2 m q a b hab⟩)
  exact ⟨data.choose, fun s => ⟨(data.choose_spec s).choose, (data.choose_spec s).choose_spec.1,
    fun x hx m q a b hab => (data.choose_spec s).choose_spec.2 x hx m trivial q a b hab⟩⟩

private theorem n04PulledFieldsInverseRawFamily_positive_input
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (RF : ∀ m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun x => f x m))
    (k : ℕ) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      (0 < k → ∀ x ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
      ∀ m (q : unitStrip) (a b : ℕ), a + b ≤ s →
        |((RF m).parameter a b q.val q.property).D k x v| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading S) base (s + d) x v) := by
  let data := n04PulledFields_currentData_rawPositive_prefix hdata hE hH hreg RF k
  exact ⟨data.choose, fun s => ⟨(data.choose_spec s).choose, (data.choose_spec s).choose_spec.1,
    fun hk x hx v m q a b hab =>
      (data.choose_spec s).choose_spec.2 k le_rfl hk x hx v m q a b hab⟩⟩

/-- The same current data supply the common raw input of the scalar prefix theorem. -/
theorem n04PulledFields_currentData_rawFamily_oneHigh
    {ι : Type*} [Fintype ι]
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : ι → Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ι → ℕ → PolarPoint → ℝ}
    (hdata : ∀ i, CurrentJetDataOn S T cell (fun _ => True) base ε (f i) (f₀ i))
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    {M : ℝ} (hM : 0 ≤ M)
    (hHM : ∀ m, T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ M)
    (hreg : ∀ i m, ContDiffOn ℝ ∞ (f₀ i m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i m, ∀ (q : unitStrip) (a b : ℕ),
      a + b ≤ s → |mixedDerivative a b (f₀ i m) q.val| ≤
        B * T.E0 (T.sample (cell m)) ^ B)
    (RF : ∀ i m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f i z m)) :
    ∃ L : ℕ → ℕ, ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m (q : unitStrip) (a b : ℕ), a + b = s → 0 < k + s →
      ∀ x ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |((RF i m).parameter a b q.val q.property).D k x v| ≤
          B * T.E0 (T.sample (cell m)) ^ B *
            parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
              oneHighVariationWeight (parameterGrading S) base
                ((if k = 0 then s - 1 else s) + L k) x v := by
  exact n04PulledFields_inverseRawBounds_oneHigh (X := Parameter S) (ι := ι)
    (f := fun i m a b q x => mixedDerivative a b (f i x m) q.val)
    (fun i m a b q => (RF i m).parameter a b q.val q.property)
    (parameterGrading S) (n07aParameterGrading_monotone S) base
    (fun m => T.E0 (T.sample (cell m)))
    (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
    hE (fun m => Real.rpow_nonneg (hH m) _) hM hHM
    (fun i => n04PulledFieldsInverseRawFamily_zero_input (hdata i) hE hH (hreg i)
      (fun s => ⟨(href s).choose, (href s).choose_spec.1,
        fun m q a b hab => (href s).choose_spec.2 i m q a b hab⟩))
    (fun i k => n04PulledFieldsInverseRawFamily_positive_input (hdata i) hE hH (hreg i) (RF i) k)

/-- The finite family uses one common low order and one common power scale. -/
theorem n04PulledFields_currentData_rawFamily_pureWord
    {ι : Type*} [Fintype ι]
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : ι → Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ι → ℕ → PolarPoint → ℝ}
    (hdata : ∀ i, CurrentJetDataOn S T cell (fun _ => True) base ε (f i) (f₀ i))
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    {M : ℝ} (hM : 0 ≤ M)
    (hHM : ∀ m, T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ M)
    (hreg : ∀ i m, ContDiffOn ℝ ∞ (f₀ i m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i m, ∀ (q : unitStrip) (a b : ℕ),
      a + b ≤ s → |mixedDerivative a b (f₀ i m) q.val| ≤
        B * T.E0 (T.sample (cell m)) ^ B)
    (RF : ∀ i m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f i z m))
    (J : ∀ i m, SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
      (fun z : Parameter S × PolarPoint => f i z.1 m z.2))
    (hinterp : HasInterpolation (parameterGrading S)) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ N : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m (x : Parameter S), x ∈ sectorNeighborhood S base ε ε → parameterGrading S low x ≤ 1 →
      ∀ q ∈ unitStrip, ∀ R : ℝ, 1 ≤ R → parameterGrading S (low + N + shift * K + 1) x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → Parameter S × PolarPoint,
      (∀ j, parameterGrading S low (v j).1 ≤ 1) →
      (∀ j, parameterGrading S (low + N + shift * K + 1) (v j).1 ≤ R) →
      (∀ j, ‖(v j).2‖ ≤ 1) →
      (∀ j, w.isState j = false → (v j).1 = 0) →
      (∀ j, w.isState j = true → (v j).2 = 0) →
        |(J i m).D n (x, q) v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
            (R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))) ^
              (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + shift * K) := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  exact n04PulledFields_inverseRawBounds_pureWord (X := Parameter S) (ι := ι) (f := f) RF
    (isOpen_sectorNeighborhood S base ε ε) (sectorNeighborhood_convex S base ε ε)
    isOpen_Ioo (convex_Ioo (0 : ℝ) 1)
    (fun i m a b => n04PulledFields_currentData_rawMixed_uniform (hdata i) hE hH (hreg i)
      (fun s => ⟨(href s).choose, (href s).choose_spec.1,
        fun m q a b hab => (href s).choose_spec.2 i m q a b hab⟩) m a b (RF i m))
    J (parameterGrading S) (n07aParameterGrading_monotone S) hinterp base
    (fun m => T.E0 (T.sample (cell m)))
    (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
    hE (fun m => Real.rpow_nonneg (hH m) _) hM hHM
    (fun i => n04PulledFieldsInverseRawFamily_zero_input (hdata i) hE hH (hreg i)
      (fun s => ⟨(href s).choose, (href s).choose_spec.1,
        fun m q a b hab => (href s).choose_spec.2 i m q a b hab⟩))
    (fun i k => n04PulledFieldsInverseRawFamily_positive_input (hdata i) hE hH (hreg i) (RF i) k)

end ContinuousFlexibility.Analysis
