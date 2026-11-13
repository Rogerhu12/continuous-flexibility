import ContinuousFlexibility.Analysis.N04SourceColumnsData

/-! Genuine selected-piece current towers, obtained by adding back the fixed reference. -/

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

/-- Add the fixed reference jet back on each selected piece. -/
def CurrentJetDataOn.negativeInverse_mixedRegularity
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (m : ℕ) (hm : P m) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun z => f z m) where
  spatial z hz := (h.1 z hz m hm).1
  parameter i j q hq :=
    (smoothDirectionsAdd (h.2.choose m hm i j ⟨q, hq⟩)
      (smoothDirections_constant (isOpen_sectorNeighborhood S base ε ε)
        (mixedDerivative i j (f₀ m) q))).congr (fun z hz => by
      rw [mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (h.1 z hz m hm).1 (h₀ m hm) i j hq]
      exact sub_add_cancel _ _)

/-- Any genuine positive-order tower of the current field agrees with
the supplied tower of its reference difference. -/
theorem CurrentJetDataOn.negativeInverse_positive_jet_eq
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip)
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative i j (f z m) q.val))
    {k : ℕ} (hk : 0 < k) {z : Parameter S}
    (hz : z ∈ sectorNeighborhood S base ε ε) (v : Fin k → Parameter S) :
    J.D k z v = (h.2.choose m hm i j q).D k z v := by
  let K := (h.2.choose m hm i j q).congr (fun z hz =>
    mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
      (h.1 z hz m hm).1 (h₀ m hm) i j q.property)
  exact (smoothDirections_D_sub_constant J K hk hz v).symm

/-- The original positive-order estimate controls any genuine current
tower, with the same low order, loss and selected-piece sample. -/
theorem CurrentJetDataOn.negativeInverse_positiveTower
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip) :
    ∀ k : ℕ, 0 < k → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading S) base (s + loss) z v := by
  intro k hk
  have ht := h.2.choose_spec.2 k
  refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
    (ht.choose_spec s).choose_spec.1, ?_⟩⟩
  intro m hm q hq i j hij J z hz v
  rw [h.negativeInverse_positive_jet_eq h₀ m hm i j ⟨q, hq⟩ J hk hz v]
  exact (ht.choose_spec s).choose_spec.2 z hz v m hm ⟨q, hq⟩ i j hij


end ContinuousFlexibility.Analysis
