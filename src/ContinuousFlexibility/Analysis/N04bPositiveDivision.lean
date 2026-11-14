module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Analysis.N04bGeometryPreservation

/-!
# Interior divided coefficients for canonical pieces

Only the `dividedDifference` field is replaced. On an open canonical
interval its boundary product is nonzero, so the three actual coefficient
differences have a unique algebraic quotient by its cube.

This construction supplies the positive-piece factorization in
`N04PartB`. It asserts neither an endpoint extension nor a uniform bound
for that quotient; those require the separate boundary-jet argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The ordinary interior quotients of the three actual coefficient
differences from the reference state. -/
def n04bInteriorDividedDifference {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : SymmetricCoefficients where
  a := fun p =>
    ((K.coefficients z m).a p - (K.coefficients (C.referenceState, 0) m).a p) /
      ((p.1 - K.left m) * (K.right m - p.1)) ^ 3
  b := fun p =>
    ((K.coefficients z m).b p - (K.coefficients (C.referenceState, 0) m).b p) /
      ((p.1 - K.left m) * (K.right m - p.1)) ^ 3
  c := fun p =>
    ((K.coefficients z m).c p - (K.coefficients (C.referenceState, 0) m).c p) /
      ((p.1 - K.left m) * (K.right m - p.1)) ^ 3

/-- Keep the physical and canonical geometry, coefficients and potential;
replace only the divided-difference field by its interior quotient. -/
def n04bWithInteriorDivision {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S) : CanonicalData S :=
  { K with dividedDifference := n04bInteriorDividedDifference C K }

/-- The frozen cubic identity holds on every open piece. Strict interior
membership supplies the two positive distances to its endpoints. -/
theorem n04bWithInteriorDivision_factorization {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    let K' := n04bWithInteriorDivision C K
    let d := (p.1 - K'.left m) * (K'.right m - p.1)
    (K'.coefficients z m).a p - (K'.coefficients (C.referenceState, 0) m).a p =
        d ^ 3 * (K'.dividedDifference z m).a p ∧
    (K'.coefficients z m).b p - (K'.coefficients (C.referenceState, 0) m).b p =
        d ^ 3 * (K'.dividedDifference z m).b p ∧
    (K'.coefficients z m).c p - (K'.coefficients (C.referenceState, 0) m).c p =
        d ^ 3 * (K'.dividedDifference z m).c p := by
  have hd : ((p.1 - K.left m) * (K.right m - p.1)) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (mul_pos (sub_pos.mpr hp.1.1) (sub_pos.mpr hp.1.2)).ne'
  dsimp only [n04bWithInteriorDivision, n04bInteriorDividedDifference]
  exact ⟨(mul_div_cancel₀ _ hd).symm, (mul_div_cancel₀ _ hd).symm,
    (mul_div_cancel₀ _ hd).symm⟩

/-- Changing the unused divided field preserves every part-A property. -/
theorem n04bWithInteriorDivision_partA {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (h : Blueprint.N04PartA D S C K base ε) :
    Blueprint.N04PartA D S C (n04bWithInteriorDivision C K) base ε :=
  h.withOperatorFields K.coefficients K.potential (n04bInteriorDividedDifference C K)

/-- Assemble the exact part-B statement from its first four clauses.
The interior normalization supplies its final positive-piece clause and
does not change any field used by the preceding clauses. -/
theorem n04bWithInteriorDivision_partB_of_parts {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hcut : CanonicalCutGeometry S C K base ε)
    (htrans : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u → ∀ m θ,
      let Wl := canonicalHeight S K z (K.cutPair m).1 u
      let Wr := canonicalHeight S K z (K.cutPair m).2 u
      Wr (K.cutRadius m, θ) = Wl (K.cutRadius m, θ) ∧
      radialPartial Wr (K.cutRadius m, θ) =
        -radialPartial Wl (K.cutRadius m, θ) -
          Wl (K.cutRadius m, θ) / (2 * K.cutRadius m))
    (hop : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m W, ContDiff ℝ ∞ W → ∀ p ∈ canonicalOpen S K m,
      canonicalOperator S K L z m W p =
        (if K.positive m then -1 else (1 : ℝ)) *
          divergenceOperator (K.coefficients z m) W p + K.potential z m p * W p)
    (hneg : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m, K.positive m = false → ∀ p ∈ canonicalOpen S K m,
      (K.coefficients z m).a p = 1 ∧ (K.coefficients z m).b p = 0 ∧
        (K.coefficients z m).c p = -p.1) :
    Blueprint.N04PartB S C L (n04bWithInteriorDivision C K) base ε := by
  refine ⟨hcut, htrans, hop, hneg, ?_⟩
  intro z _ _ m _ p hp
  exact n04bWithInteriorDivision_factorization C K z m hp

/-- In particular, an existing part-B witness retains all its identities
after replacing its divided field by the actual interior quotient. -/
theorem n04bWithInteriorDivision_partB {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ} (h : Blueprint.N04PartB S C L K base ε) :
    Blueprint.N04PartB S C L (n04bWithInteriorDivision C K) base ε :=
  n04bWithInteriorDivision_partB_of_parts h.1 h.2.1 h.2.2.1 h.2.2.2.1

end ContinuousFlexibility.Statements
