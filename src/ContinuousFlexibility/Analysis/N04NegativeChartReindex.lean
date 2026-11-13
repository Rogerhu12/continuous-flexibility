import ContinuousFlexibility.Analysis.N04NegativeGeometryReductions
import Mathlib.Basic.Denumerable

/-!
# Reindexing only the selected negative pieces

The negative halves have their own countable enumeration. Scalar calculus
on that enumeration therefore applies to every listed piece without making
any assertion about the unrelated positive atlas. Both directions of the
transport preserve the original material sample and actual scalar function.
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

section ScalarData

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Enumerating selected pieces retains all constants and derivative losses. -/
theorem CurrentJetDataOn.reindex_selected
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (r : ℕ → ℕ) (hr : ∀ n, P (r n)) :
    CurrentJetDataOn S T (cell ∘ r) (fun _ => True) base ε
      (fun z n => f z (r n)) (fun n => f₀ (r n)) := by
  refine ⟨fun z hz n _ => h.1 z hz (r n) (hr n),
    fun n _ i j q => h.2.choose (r n) (hr n) i j q, ?_, ?_⟩
  · have hv := h.2.choose_spec.1
    refine ⟨hv.choose, fun s => ⟨(hv.choose_spec s).choose,
      (hv.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz n _ q i j hij
    exact (hv.choose_spec s).choose_spec.2 z hz (r n) (hr n) q i j hij
  · intro k
    have ht := h.2.choose_spec.2 k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz v n _ q i j hij
    exact (ht.choose_spec s).choose_spec.2 z hz v (r n) (hr n) q i j hij

/-- Covering the selected pieces transfers the same actual towers back.
The index choice is made before the spatial and parameter orders. -/
theorem CurrentJetDataOn.of_reindex_selected
    (r : ℕ → ℕ) (hr : ∀ m, P m → ∃ n, r n = m)
    (h : CurrentJetDataOn S T (cell ∘ r) (fun _ => True) base ε
      (fun z n => f z (r n)) (fun n => f₀ (r n))) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  let index (m : ℕ) (hm : P m) : ℕ := (hr m hm).choose
  have hindex (m : ℕ) (hm : P m) : r (index m hm) = m := (hr m hm).choose_spec
  let J : ∀ m, P m → ∀ i j (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val) :=
    fun m hm i j q => (h.2.choose (index m hm) trivial i j q).congrOn
      (fun z _ => congrArg
        (fun n => mixedDerivative i j (fun y => f z n y - f₀ n y) q.val)
        (hindex m hm))
  refine ⟨fun z hz m hm => ?_, J, ?_, ?_⟩
  · simpa only [hindex] using h.1 z hz (index m hm) trivial
  · have hv := h.2.choose_spec.1
    refine ⟨hv.choose, fun s => ⟨(hv.choose_spec s).choose,
      (hv.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz m hm q i j hij
    simpa only [Function.comp_apply, hindex] using
      (hv.choose_spec s).choose_spec.2 z hz (index m hm) trivial q i j hij
  · intro k
    have ht := h.2.choose_spec.2 k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz v m hm q i j hij
    change |(h.2.choose (index m hm) trivial i j q).D k z v| ≤ _
    simpa only [Function.comp_apply, hindex] using
      (ht.choose_spec s).choose_spec.2 z hz v (index m hm) trivial q i j hij

end ScalarData

/-- One enumeration of the component and orientation pair. -/
def n04NegativeChartPairEnumeration : ℕ ≃ ℕ × Bool :=
  Classical.choice nonempty_equiv_of_countable

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Only the retained negative halves are enumerated. -/
def negativeChartPiece (n : ℕ) : ℕ :=
  G.e.symm (.inl (n04NegativeChartPairEnumeration n))

theorem negativeChartPiece_negative
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (n : ℕ) :
    G.Neg η (G.negativeChartPiece n) :=
  (G.neg_iff_inl η _).mpr ⟨n04NegativeChartPairEnumeration n, G.e.apply_symm_apply _⟩

theorem negativeChartPiece_covers
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m) :
    ∃ n, G.negativeChartPiece n = m := by
  obtain ⟨j, hj⟩ := (G.neg_iff_inl η m).mp hm
  refine ⟨n04NegativeChartPairEnumeration.symm j, ?_⟩
  apply G.e.injective
  simpa only [negativeChartPiece, Equiv.apply_symm_apply] using hj.symm

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.of_reindex_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.of_reindex_selected
