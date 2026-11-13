import ContinuousFlexibility.Analysis.N04PrincipalPositiveIndex
import ContinuousFlexibility.Analysis.N04PrincipalPositiveReference

/-!
# Orientation and reference ellipticity of the supplied positive atlas

The retained transport matching proves the chart orientation for the
same actual maps. Consequently its inverse determinant is positive and
the principal formula can use an ordinary reciprocal. The reference
leading coefficient is positive independently of every current bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The actual positive fields retain the full range certificate of the
fixed reference chart composed with the supplied transport. -/
theorem n04PrincipalPositive_rangeGeometry {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : AnnularState (G.S η) × ℝ}
    (hz : z ∈ stateNeighborhood (G.S η) (G.C η) b ε)
    (hs : stateSector (G.S η) z.1) {m : ℕ} (hm : G.Pos η m) :
    PositiveChartRangeGeometry ((G.V η).chart z m) ((G.V η).inverseChart z m)
      ((G.V η).height z m) ((G.V η).physicalLeft m) ((G.V η).physicalRight m) 0 1 := by
  have hi := G.n04PrincipalDivided_positive_index η hm
  let i := hi.choose
  have him : G.e m = Sum.inr i := hi.choose_spec
  have hmatching := h.2.2.2.2.2.choose_spec.choose_spec.choose_spec.2
  have hg := wholePositiveReferenceGauge_geometry (h.2.2.2.1 i).1
    (wholePositiveChartGeometry_of_matching (hmatching z hz hs i))
  have hf := n04WholeReferenceGaugeAtlasData_positive_fields
    G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
    (fun j => positiveReferenceCylinderChart (G.Y j))
    (fun j => positiveReferenceCylinderInverse (G.Y j))
    (fun j p => G.H j p.1) G.τ G.σ G.Q G.N z m i him
  have hpl : (G.V η).physicalLeft m = n04PositiveLeft i := hf.2.2.1
  have hpr : (G.V η).physicalRight m = n04PositiveRight i := hf.2.2.2.1
  have hF : (G.V η).chart z m = wholePositiveReferenceGaugeChart
      (positiveReferenceCylinderChart (G.Y i)) (G.σ z i) :=
    hf.2.2.2.2.2.2.2.1
  have hI : (G.V η).inverseChart z m = wholePositiveReferenceGaugeInverse
      (G.τ z i) (positiveReferenceCylinderInverse (G.Y i)) :=
    hf.2.2.2.2.2.2.2.2.1
  have hH : (G.V η).height z m = wholePositiveReferenceGaugeHeight
      (fun p => G.H i p.1) (G.σ z i) (G.Q z i) :=
    hf.2.2.2.2.2.2.2.2.2.1
  rw [hF, hI, hH, hpl, hpr]
  exact hg

/-- The inverse Jacobian on a positive piece is positive everywhere. -/
theorem n04PrincipalPositive_inverseJacobian_pos {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : AnnularState (G.S η) × ℝ}
    (hz : z ∈ stateNeighborhood (G.S η) (G.C η) b ε)
    (hs : stateSector (G.S η) z.1) {m : ℕ} (hm : G.Pos η m) (p : PolarPoint) :
    0 < planeJacobian ((G.V η).inverseChart z m) p := by
  have hg := G.n04PrincipalPositive_rangeGeometry h η hz hs hm
  have hinverse : (G.V η).chart z m ∘ (G.V η).inverseChart z m =ᶠ[𝓝 p]
      (id : PolarPoint → PolarPoint) := Filter.Eventually.of_forall hg.right_inverse
  have hprod := planeJacobian_inverse_mul_of_germ
    (hg.inverse_smooth.differentiable (by simp) p)
    (hg.chart_smooth.differentiable (by simp) ((G.V η).inverseChart z m p)) hinverse
  by_contra hnot
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    (hg.jacobian_positive ((G.V η).inverseChart z m p)).le (le_of_not_gt hnot)
  rw [hprod] at hnonpos
  exact (not_le_of_gt zero_lt_one) hnonpos

/-- Reference positivity is a qualitative property of the constructed
reference-gauged operator, and holds on every piece. -/
theorem n04PrincipalPositive_reference_principalA_pos {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen (G.S η) (G.V η) m) :
    0 < ((G.V η).coefficients (G.ref η) m).a p := by
  have hA : CanonicalGeometry G.W.D G.W.S G.W.C
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N) b ε :=
    (G.n04PrincipalPositive_admissible_parts h η).1
  have hqual := n04WholeReferenceGaugeAtlasData_actual_referencePrincipal_qualitative
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ G.e G.X.cell
    G.Y G.H G.τ G.σ G.Q G.N h.2.1 h.2.2.2.2.1
    (fun i => (h.2.2.2.1 i).1) hA
  exact (hqual m p hp).1

theorem n04PrincipalPositive_reference_principalA_atom_pos {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (m : ℕ) (q : unitStrip) : 0 < G.atomRef η .principalA m q.val := by
  have hA := (G.n04PrincipalPositive_admissible_parts h η).1
  have hlen : 0 < (G.V η).right m - (G.V η).left m :=
    sub_pos.mpr (hA.referenceBounds m).2.1
  have hq : canonicalUnitPoint (G.V η) m q.val ∈ canonicalOpen (G.S η) (G.V η) m := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · change (G.V η).left m < (G.V η).left m + _
      exact lt_add_of_pos_right _ (mul_pos hlen q.property.1.1)
    · have ht := mul_lt_of_lt_one_right hlen q.property.1.2
      change (G.V η).left m + _ < (G.V η).right m
      linarith only [ht]
  exact G.n04PrincipalPositive_reference_principalA_pos h η m hq

end N04RealizationGauge

end ContinuousFlexibility.Analysis
