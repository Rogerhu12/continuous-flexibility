module

public import ContinuousFlexibility.Analysis.N04PrincipalPositiveOrientation
public import ContinuousFlexibility.Analysis.N04PrincipalPositiveReferenceJets

/-!
# Reference jets of the signed inverse determinant

Positive orientation identifies the signed inverse determinant and its
reciprocal with the two original Jacobian atoms evaluated at the actual
reference inverse point. Thus both factors retain the same-piece
reference envelopes at every spatial order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04PrincipalPositive_reference_inverseJacobian_composedAtom {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {m : ℕ} (hm : G.Pos η m) (inverse : Bool) :
    (fun q => if inverse then (planeJacobian ((G.V η).inverseChart (G.ref η) m) q)⁻¹
      else planeJacobian ((G.V η).inverseChart (G.ref η) m) q) =
    (fun q => G.atomRef η (if inverse then .jacobian else .jacobianInverse) m
      (G.n04PrincipalPositive_referenceUnitInverse η m q)) := by
  have hz : G.ref η ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    reference_mem_stateNeighborhood (G.S η) (G.C η) b h.2.1
  have hs : stateSector (G.S η) (G.C η).referenceState :=
    G.W.through03.1.1.2.2.1.stateSector
  have hg := G.n04PrincipalPositive_rangeGeometry h η hz hs hm
  let F := (G.V η).chart (G.ref η) m
  let I := (G.V η).inverseChart (G.ref η) m
  funext q
  have hinverse : F ∘ I =ᶠ[𝓝 q] (id : PolarPoint → PolarPoint) :=
    Filter.Eventually.of_forall hg.right_inverse
  have hprod := planeJacobian_inverse_mul_of_germ
    (hg.inverse_smooth.differentiable (by simp) q)
    (hg.chart_smooth.differentiable (by simp) (I q)) hinverse
  have hInv : (planeJacobian I q)⁻¹ = planeJacobian F (I q) :=
    inv_eq_of_mul_eq_one_left hprod
  have hJ : planeJacobian I q = (planeJacobian F (I q))⁻¹ := by
    rw [← hInv, inv_inv]
  have hpoint : physicalUnitPoint (G.V η) m
      (G.n04PrincipalPositive_referenceUnitInverse η m q) = I q := by
    simpa only [G.n04PrincipalPositive_unitPoint_eq η hm, id_eq] using
      G.n04PrincipalPositive_referenceUnitInverse_point h η m q
  have hJpos : 0 < planeJacobian F (I q) := hg.jacobian_positive (I q)
  cases inverse
  · simp only [Bool.false_eq_true, ↓reduceIte, atomRef, atom, hpoint]
    change planeJacobian I q = |planeJacobian F (I q)|⁻¹
    rw [abs_of_pos hJpos]
    exact hJ
  · simp only [↓reduceIte, atomRef, atom, hpoint]
    change (planeJacobian I q)⁻¹ = |planeJacobian F (I q)|
    rw [abs_of_pos hJpos]
    exact hInv

/-- The reference inverse determinant and its reciprocal are smooth and
have full uniform coefficient-power bounds on positive pieces. -/
theorem n04PrincipalPositive_reference_inverseJacobian_jets {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    (∀ m, G.Pos η m → ∀ inverse : Bool, ContDiffOn ℝ ∞
      (fun q => if inverse then (planeJacobian ((G.V η).inverseChart (G.ref η) m) q)⁻¹
        else planeJacobian ((G.V η).inverseChart (G.ref η) m) q) unitStrip) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, G.Pos η m →
      ∀ (inverse : Bool) (q : unitStrip) i j, i + j ≤ s →
        |mixedDerivative i j
          (fun y => if inverse then (planeJacobian ((G.V η).inverseChart (G.ref η) m) y)⁻¹
            else planeJacobian ((G.V η).inverseChart (G.ref η) m) y) q.val| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  refine ⟨?_, fun s => ?_⟩
  · intro m hm inverse
    rw [G.n04PrincipalPositive_reference_inverseJacobian_composedAtom h η hm inverse]
    exact (href.1 m _).1.comp
      (G.n04PrincipalPositive_referenceUnitInverse_smooth η href m)
      (G.n04PrincipalPositive_referenceUnitInverse_maps h η m)
  · have hb := G.n04PrincipalPositive_reference_composedAtom_bounds h η href s
    refine ⟨hb.choose, hb.choose_spec.1, ?_⟩
    intro m hm inverse q i j hij
    rw [G.n04PrincipalPositive_reference_inverseJacobian_composedAtom h η hm inverse]
    exact hb.choose_spec.2 m _ q i j hij

end N04RealizationGauge

end ContinuousFlexibility.Analysis
