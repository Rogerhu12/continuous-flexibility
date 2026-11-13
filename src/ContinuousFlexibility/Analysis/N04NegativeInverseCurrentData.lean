import ContinuousFlexibility.Analysis.N04NegativeInverseCurrentTowers
import ContinuousFlexibility.Analysis.N04SourceColumnsPrefix
import ContinuousFlexibility.Analysis.N04NegativeInversePrefixPower

/-! Finite prefixes of selected current jets with one fixed low order. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Selected current data admit raw interpolation bounds with one low
order before the parameter prefix. The finite shift may depend on that
prefix; the low order and the height exponent do not. -/
theorem CurrentJetDataOn.negativeInverse_prefix_power
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, P m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (f₀ m) q| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    ∃ b : ℕ, base ≤ b ∧ ∀ K : ℕ, ∃ shift : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ k, k ≤ K → ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j,
      i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S b z ≤ 1 →
      ∀ v : Fin k → Parameter S, (∀ l, parameterGrading S b (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading S (b + s + shift * K + 1) z ≤ R →
        (∀ l, parameterGrading S (b + s + shift * K + 1) (v l) ≤ R) →
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
            R ^ (((i + j + shift * k : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  let I : Type := {m : ℕ // P m}
  let RF (m : I) := h.negativeInverse_mixedRegularity h₀ m.val m.property
  have ht := h.negativeInverse_fullTower hD hT h₀ href hE
  let L : ℕ → ℕ := fun k => (ht k).choose
  have hb (k s : ℕ) : ∃ B : ℝ, 0 < B ∧
      ∀ m : I, ∀ q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |((RF m).parameter i j q hq).D k z v| ≤
          B * T.E0 (T.sample (cell m.val)) ^ B *
            parameterHeightWeight (T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) k *
              oneHighVariationWeight (parameterGrading S) base (s + L k) z v := by
    have hs := (ht k).choose_spec s
    exact ⟨hs.choose, hs.choose_spec.1,
      fun m q hq i j hij z hz v => hs.choose_spec.2 m.val m.property q hq i j hij
        ((RF m).parameter i j q hq) z hz v⟩
  obtain ⟨b, hbase, hprefix⟩ := n04SourceColumns_prefix_power (parameterGrading S)
    (tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl))
    hI base L (fun m : I => T.E0 (T.sample (cell m.val)))
    (fun k m => parameterHeightWeight (T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) k)
    (fun m => hE m.val)
    (fun k m => parameterHeightWeight_nonneg (Real.rpow_nonneg (hH m.val) _) k)
    (fun m z => f z m.val) RF hb
  refine ⟨b, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hshift s
  refine ⟨B, hB, ?_⟩
  intro k hk m hm q hq i j hij J z hz hlow v hv R hR hzR hvR
  have he := congrArg (fun A : (Parameter S) [×k]→L[ℝ] ℝ => A v)
    (J.unique ((RF ⟨m, hm⟩).parameter i j q hq) k z hz)
  rw [he]
  exact hbound k hk ⟨m, hm⟩ q hq i j hij z hz hlow v hv R hR hzR hvR

/-- The selected current prefix with the exact inverse-recursion degree.
The base is fixed once; each positive joint order saves one spatial derivative. -/
theorem CurrentJetDataOn.negativeInverse_sharpPrefix_power
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, P m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (f₀ m) q| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    ∃ b : ℕ, base ≤ b ∧ ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧ ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ k, k ≤ K → ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j,
      i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S b z ≤ 1 →
      ∀ v : Fin k → Parameter S, (∀ l, parameterGrading S b (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading S (b + s + shift * K + 1) z ≤ R →
        (∀ l, parameterGrading S (b + s + shift * K + 1) (v l) ≤ R) →
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
            R ^ (((i + j + shift * k - 1 : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  let I : Type := {m : ℕ // P m}
  let RF (m : I) := h.negativeInverse_mixedRegularity h₀ m.val m.property
  have ht := h.negativeInverse_fullTower hD hT h₀ href hE
  let L : ℕ → ℕ := fun k => (ht k).choose
  have hb (k s : ℕ) : ∃ B : ℝ, 0 < B ∧
      ∀ m : I, ∀ q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |((RF m).parameter i j q hq).D k z v| ≤
          B * T.E0 (T.sample (cell m.val)) ^ B *
            parameterHeightWeight (T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) k *
              oneHighVariationWeight (parameterGrading S) base (s + L k) z v := by
    have hs := (ht k).choose_spec s
    exact ⟨hs.choose, hs.choose_spec.1,
      fun m q hq i j hij z hz v => hs.choose_spec.2 m.val m.property q hq i j hij
        ((RF m).parameter i j q hq) z hz v⟩
  obtain ⟨b, hbase, hprefix⟩ := n04NegativeInverse_scalar_prefix_power (parameterGrading S)
    (tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl))
    hI base L (fun m : I => T.E0 (T.sample (cell m.val)))
    (fun k m => parameterHeightWeight (T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) k)
    (fun m => hE m.val)
    (fun k m => parameterHeightWeight_nonneg (Real.rpow_nonneg (hH m.val) _) k)
    (fun m z => f z m.val) RF hb
  refine ⟨b, hbase, fun K => ?_⟩
  obtain ⟨shift, hshiftOne, hshift⟩ := hprefix K
  refine ⟨shift, hshiftOne, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hshift s
  refine ⟨B, hB, ?_⟩
  intro k hk m hm q hq i j hij J z hz hlow v hv R hR hzR hvR
  have he := congrArg (fun A : (Parameter S) [×k]→L[ℝ] ℝ => A v)
    (J.unique ((RF ⟨m, hm⟩).parameter i j q hq) k z hz)
  rw [he]
  exact hbound k hk ⟨m, hm⟩ q hq i j hij z hz hlow v hv R hR hzR hvR

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_prefix_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_prefix_power

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_sharpPrefix_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_sharpPrefix_power
