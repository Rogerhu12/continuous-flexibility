import ContinuousFlexibility.Analysis.N04PrincipalPositiveGeometry

/-!
# The fixed unit interval of every positive whole piece

These are the actual stored endpoints, before any principal estimate.
The shared index lemmas are used by both the principal and divided fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04PrincipalDivided_positive_index
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) {m : ℕ} (hm : G.Pos η m) :
    ∃ i, G.e m = Sum.inr i := by
  change n04WholePiecePositive (G.e m) = true at hm
  cases hi : G.e m with
  | inl j => simp only [hi, n04WholePiecePositive, Bool.false_eq_true] at hm
  | inr i => exact ⟨i, hi⟩

theorem n04PrincipalDivided_positive_endpoints
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) {m : ℕ} (hm : G.Pos η m) :
    (G.V η).left m = 0 ∧ (G.V η).right m = 1 := by
  have hi := G.n04PrincipalDivided_positive_index η hm
  have hf := n04WholeReferenceGaugeAtlasData_positive_fields
    G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
    (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i))
    (fun i p => G.H i p.1) G.τ G.σ G.Q G.N
    (G.W.C.referenceState, 0) m hi.choose hi.choose_spec
  exact ⟨hf.1, hf.2.1⟩

theorem n04PrincipalPositive_unitPoint_eq
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) {m : ℕ} (hm : G.Pos η m) :
    canonicalUnitPoint (G.V η) m = id := by
  have he := G.n04PrincipalDivided_positive_endpoints η hm
  funext q
  simp only [canonicalUnitPoint, he.1, he.2, sub_zero, one_mul, zero_add, id_eq]

end N04RealizationGauge

end ContinuousFlexibility.Analysis
