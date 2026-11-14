module

public import ContinuousFlexibility.Analysis.N07aUnitCoefficientRows

/-!
# Fourier blocks of the actual geometric coefficient differences

The bounds below are extracted from the original current geometric
jets. They keep the exact H^(3/4) gain and exactly one state seminorm.
The derivative loss is fixed; no relative-operator estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

def n07aDifferenceBlockBudget (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (loss s : ℕ) (B : ℝ) (z : Parameter S) (m : ℕ) : ℝ :=
  B * T.E0 (T.sample (K.cell m)) ^ B * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
    parameterGrading S (s + 4 + loss) z

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07a_actualDifference_jet_block_bounds
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m a x, x ∈ Ioo (0 : ℝ) 1 →
      ∀ i k : ℕ, i + k ≤ 1 → ∀ l j : ℕ,
      let f := n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m a) i k x
      let W := (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s
      let M := 8 * n07aDifferenceBlockBudget T S K loss s B z m * n07aAngularTail ((j : ℤ) - l)
      W * |n07aCosineMatrixEntry f l j| ≤ M ∧
      W * |n07aSineMatrixEntry f l j| ≤ M ∧
      W * |((l : ℝ) - j) * n07aCosineMatrixEntry f l j| ≤ M ∧
      W * |((l : ℝ) - j) * n07aSineMatrixEntry f l j| ≤ M := by
  let loss : ℕ := hcur.2.1.choose
  have hdiff := hcur.2.1.choose_spec
  refine ⟨loss, fun s => ?_⟩
  let B : ℝ := (hdiff (s + 4)).choose
  have hB : 0 < B := (hdiff (s + 4)).choose_spec.1
  have hBb := (hdiff (s + 4)).choose_spec.2
  refine ⟨B, hB, fun z hz m a x hx i k hi l j => ?_⟩
  let f := n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m a) i k x
  let M := n07aDifferenceBlockBudget T S K loss s B z m
  have hf₀ := n07aUnitDifferenceAtom_contDiff href hcur hz m a
  have hfp₀ := n07aUnitDifferenceAtom_periodic href hcur hz m a
  have hf : ContDiff ℝ ∞ f := n07aUnitJetRow_contDiff hf₀ i k hx
  have hfp : Function.Periodic f Real.pi := n07aUnitJetRow_periodic hfp₀ i k hx
  have hbnd (q : ℕ) (hq : i + (q + k) ≤ s + 4) (θ : ℝ) : |iteratedDeriv q f θ| ≤ M := by
    have h := hBb z hz m a ⟨(x, θ), ⟨hx, mem_univ _⟩⟩ i (q + k) hq
    change |mixedDerivative i (q + k) (n07aUnitDifferenceAtom D T S C L K z m a) (x, θ)| ≤ M at h
    rw [show f = n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m a) i k x from rfl,
      n07aUnitJetRow_iteratedDeriv hf₀ i k q hx θ]
    exact h
  have h₀ : ∀ θ, |f θ| ≤ M := by
    simpa only [iteratedDeriv_zero] using hbnd 0 (by omega)
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (h₀ 0)
  have hr := n07a_circleMatrix_weighted_bounds hf hfp s hM hM h₀ (hbnd (s + 2) (by omega)) l j
  have hc := n07a_circleMatrix_commutator_bounds hf hfp s hM hM h₀ (hbnd (s + 3) (by omega)) l j
  have he : 4 * (M + M) * n07aAngularTail ((j : ℤ) - l) =
      8 * M * n07aAngularTail ((j : ℤ) - l) := by ring
  exact ⟨hr.1.trans_eq he, hr.2.trans_eq he, hc.1.trans_eq he, hc.2.trans_eq he⟩

theorem n07a_actualDifference_block_bounds
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m a x, x ∈ Ioo (0 : ℝ) 1 →
      ∀ i : ℕ, i ≤ 1 → ∀ l j : ℕ,
      let f := n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m a) i 0 x
      let W := (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s
      let M := 8 * n07aDifferenceBlockBudget T S K loss s B z m * n07aAngularTail ((j : ℤ) - l)
      W * |n07aCosineMatrixEntry f l j| ≤ M ∧
      W * |n07aSineMatrixEntry f l j| ≤ M ∧
      W * |((l : ℝ) - j) * n07aCosineMatrixEntry f l j| ≤ M ∧
      W * |((l : ℝ) - j) * n07aSineMatrixEntry f l j| ≤ M := by
  let h := n07a_actualDifference_jet_block_bounds href hcur
  let loss : ℕ := h.choose
  refine ⟨loss, fun s => ?_⟩
  let B : ℝ := (h.choose_spec s).choose
  have hB : 0 < B := (h.choose_spec s).choose_spec.1
  have hbound := (h.choose_spec s).choose_spec.2
  exact ⟨B, hB, fun z hz m a x hx i hi l j => hbound z hz m a x hx i 0 (by omega) l j⟩

end ContinuousFlexibility.Analysis
