import ContinuousFlexibility.Analysis.N04PrincipalDividedData
import ContinuousFlexibility.Analysis.N04PrincipalDividedActualReferenceGaugeEndpointJets
import ContinuousFlexibility.Analysis.N04PrincipalDividedRadialGaugePrincipalDifferenceExtension
import ContinuousFlexibility.Analysis.N04PrincipalPositiveIndex
import ContinuousFlexibility.Analysis.N04RealizationActualCubicFactor
import ContinuousFlexibility.Analysis.CanonicalReferenceDividedJets

/-!
# Divided atoms of the supplied reference-gauged atlas

All positive endpoints in a retained start are interior simple roots.
Transport matching gives the actual numerator's zero jets there. The fixed
reference gauge transports these jets and supplies a smooth representative
on the closed unit cylinder. The current-data division theorem then applies
to the stored quotient; the negative and reference atoms are zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

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

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

private theorem n04PrincipalDivided_principal_atom (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (w : AnnularState (G.S η) × ℝ) (m : ℕ) (v : Fin 3) (q : PolarPoint) :
    atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) w m
        (n07aCubicPrincipalAtom v) q =
      canonicalCoefficientComponent v ((G.V η).coefficients w m)
        (canonicalUnitPoint (G.V η) m q) := by
  fin_cases v <;> rfl

/-- The actual positive numerator has a smooth representative with its
three genuine zero jets at each endpoint. -/
theorem n04PrincipalDivided_positive_representative {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Pos η m) (v : Fin 3) :
    ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (fun q => G.atomFamily η (n07aCubicPrincipalAtom v) z m q -
        G.atomRef η (n07aCubicPrincipalAtom v) m q) unitStrip ∧
      ∀ side : Bool, ∀ θ k, k ≤ 2 →
        iteratedDeriv k (fun t : ℝ => F (t, θ)) (if side then 1 else 0) = 0 := by
  let w : AnnularState G.W.S × ℝ := G.lift η z
  have hw : w ∈ stateNeighborhood G.W.S G.W.C b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs : stateSector G.W.S w.1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hw₀ : w ∈ stateNeighborhood G.W.S G.W.C G.W.base G.W.ε :=
    stateNeighborhood_mono G.W.S G.W.C h.1 h.2.2.1 hw
  have hi := G.n04PrincipalDivided_positive_index η hm
  let i := hi.choose
  have him : G.e m = Sum.inr i := hi.choose_spec
  have hmatching := h.2.2.2.2.2.choose_spec.choose_spec.choose_spec.2
  have hmatch := hmatching w hw hs i
  have hreference := h.2.2.2.2.1 i
  have hrefState := reference_mem_stateNeighborhood G.W.S G.W.C b h.2.1
  have hrefSector := G.W.through03.1.1.2.2.1.stateSector
  have hgeometry₀ := wholePositiveChartGeometry_of_matching
    (hmatching (G.W.C.referenceState, 0) hrefState hrefSector i)
  have hgeometry := wholePositiveChartGeometry_of_matching hmatch
  have hG := (h.2.2.2.1 i).1
  have hleft : G.W.D.a < n04PositiveLeft i := (G.W.roots i false).1.1
  have hright : n04PositiveRight i < G.W.D.b := (G.W.roots i true).1.2
  have hlr := (n04PositiveComponent_bounds
    (G.W.radial.1.2.2.1.1.continuous_deriv (by simp)) i).2.1
  have hA := G.W.field.smooth_coefficients w hw₀ hs
  have hA₀ := G.W.field.smooth_coefficients (G.W.C.referenceState, 0)
    (reference_mem_stateNeighborhood G.W.S G.W.C G.W.base G.W.ε_pos) hrefSector
  have hrep := exists_referenceGaugePrincipal_difference_extension
    hleft hlr hright hgeometry hgeometry₀
    hreference.1 hreference.2.1 hreference.2.2 hG
    hA.1 hA.2.1 hA.2.2 hA₀.1 hA₀.2.1 hA₀.2.2
  let F := hrep.choose
  have hF := hrep.choose_spec.1
  have he := hrep.choose_spec.2
  have hend := G.n04PrincipalDivided_positive_endpoints η hm
  have hunit (q : PolarPoint) : canonicalUnitPoint (G.V η) m q = q := by
    unfold canonicalUnitPoint
    rw [hend.1, hend.2]
    simp only [sub_zero, one_mul, zero_add, Prod.mk.eta]
  have hcoef (u : AnnularState G.W.S × ℝ) :
      (G.V η).coefficients u m =
        inverseChartPrincipalCoefficients (G.W.L.coefficients u)
          (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart (G.Y i)) (G.σ u i))
          (wholePositiveReferenceGaugeInverse (G.τ u i) (positiveReferenceCylinderInverse (G.Y i)))
          (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => G.H i p.1)
            (G.σ u i) (G.Q u i)) := by
    have hf := n04WholeReferenceGaugeAtlasData_positive_fields
      G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
      (fun i => positiveReferenceCylinderChart (G.Y i))
      (fun i => positiveReferenceCylinderInverse (G.Y i))
      (fun i p => G.H i p.1) G.τ G.σ G.Q G.N u m i him
    exact hf.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨F v, hF v, ?_, ?_⟩
  · intro q hq
    have hqclosed : q ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) :=
      ⟨⟨hq.1.1.le, hq.1.2.le⟩, mem_univ _⟩
    have hqeq := (he v q hqclosed).eq_of_nhds
    change F v q = atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
      (G.lift η z) m (n07aCubicPrincipalAtom v) q -
      atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
        (G.ref η) m (n07aCubicPrincipalAtom v) q
    rw [G.n04PrincipalDivided_principal_atom, G.n04PrincipalDivided_principal_atom,
      hunit, hcoef, hcoef]
    exact hqeq
  · intro side θ k hk
    let t : ℝ := if side then 1 else 0
    have ht : t ∈ Icc (0 : ℝ) 1 := by cases side <;> exact ⟨by norm_num, by norm_num⟩
    have hg := (he v (t, θ) ⟨ht, mem_univ _⟩).comp_tendsto
      ((continuous_id.prodMk continuous_const).tendsto t)
    have hinterior : n04PositiveEndpoint i side ≠ (if side then G.W.D.b else G.W.D.a) := by
      cases side
      · exact ne_of_gt hleft
      · exact ne_of_lt hright
    have hzero := radialBoundaryJet_sub_eq_zero_of_finiteFullJetMatch
      (n04Coordinates_referenceGaugePrincipal_endpoint_jets
        G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ hw₀ hs (G.X.src i)
        hmatch hgeometry₀ hreference.1 hreference.2.1 hreference.2.2 hG
        side hinterior θ v) (hk.trans (by decide : 2 ≤ 3))
    exact (hg.iteratedDeriv k).eq_of_nhds.trans hzero

theorem n04PrincipalDivided_reference_zero
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (v : Fin 3) :
    G.atomRef η (n07aCubicDividedAtom v) m = fun _ => 0 := by
  fin_cases v <;> funext q <;>
    simp only [atomRef, ref, V, C, geometryReplaceAuxiliaryColumn,
      canonicalReplaceAuxiliaryColumn, n04RealizationAtlas, n04WholeReferenceGaugeAtlasData,
      n07aCubicDividedAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      atom, n04bWithInteriorDivision, n04bInteriorDividedDifference, sub_self, zero_div, ite_self]

/-- Each of the three actual divided atoms follows from the corresponding
positive principal current data on the same neighborhood. -/
theorem n04PrincipalDivided_data {b : ℕ} {ε : ℝ} (h : G.Admissible b ε)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (v : Fin 3)
    (hprincipal : G.Data η (G.Pos η) b ε
      (G.atomFamily η (n07aCubicPrincipalAtom v)) (G.atomRef η (n07aCubicPrincipalAtom v))) :
    G.Data η (fun _ => True) b ε
      (G.atomFamily η (n07aCubicDividedAtom v)) (G.atomRef η (n07aCubicDividedAtom v)) := by
  apply n04PrincipalDivided_currentData (G.Pos η) hprincipal
    (fun m => href.1 m (n07aCubicPrincipalAtom v)) (G.cost_nonneg η).2.2
    (G.cost_nonneg η).2.1
    (fun m hm z hz => G.n04PrincipalDivided_positive_representative h η hz hm v)
    ?_ ?_ (fun m => G.n04PrincipalDivided_reference_zero η m v)
  · intro m hm z hz q hq
    have hend := G.n04PrincipalDivided_positive_endpoints η hm
    have hrefconds : referenceStateConditions G.W.D (G.S η) (G.C η) :=
      G.W.through03.1.1.2.2.1
    have hf := n04Realization_unitDifference_cubic_factor
      (G.n04PrincipalPositive_admissible_parts h η).2.1 hrefconds h.2.1 hz hm
      (by rw [hend.1, hend.2]; exact zero_lt_one) v hq
    change G.atomFamily η (n07aCubicPrincipalAtom v) z m q -
        G.atomRef η (n07aCubicPrincipalAtom v) m q =
      ((G.V η).right m - (G.V η).left m) ^ 6 * (q.1 * (1 - q.1)) ^ 3 *
        (G.atomFamily η (n07aCubicDividedAtom v) z m q -
          G.atomRef η (n07aCubicDividedAtom v) m q) at hf
    rw [G.n04PrincipalDivided_reference_zero η m v] at hf
    simpa only [hend.1, hend.2, sub_zero, one_pow, one_mul] using hf
  · intro m hm z hz q hq
    have hn : (G.V η).positive m = false := by
      cases he : (G.V η).positive m
      · exact he
      · exact False.elim (hm he)
    fin_cases v <;>
      simp only [atomFamily, n07aCubicDividedAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, atom, hn, Bool.false_eq_true, ↓reduceIte]

end N04RealizationGauge

end ContinuousFlexibility.Analysis
