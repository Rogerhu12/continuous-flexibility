import ContinuousFlexibility.Analysis.N04RealizationPrimitiveFactorEnvelopes

/-!
# The nine actual material direction fields

The current direction is one column of the inverse differential. Both
reference directions use one arbitrary vector in the same transported
continuous linear maps. The material components and exact density drift
then follow from the actual factor certificate on the original piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}

theorem n04Realization_primitiveDirection_envelopes
    {X : Type*} (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (z : X → AnnularState S × ℝ) (m : X → ℕ) (p : X → PolarPoint)
    (hz : ∀ x, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x, stateSector S (z x).1)
    (hp : ∀ x, n07bMaterialRadiusChart T (p x) ∈ physicalPieceOpen S K (z x) (m x))
    (hE : ∀ x, T.E0 (T.radius (p x).1) ≤ W x) (N : ℕ)
    (H : N04RealizationPrimitiveFactorEnvelopes X T S C K W z m p N) :
    ∀ i j : Fin 3, ∀ k : ℕ, k ≤ N → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ k
        (canonicalPrimitiveField D T C K (z x) (m x) (.inl (i, j)) ∘
          n07bMaterialRadiusChart T) (p x)‖) := by
  have hR := n07bMaterialRadiusChart_contDiff hT
  let Q : X → PolarPoint → PolarPoint := fun x => K.chart (z x) (m x) ∘ n07bMaterialRadiusChart T
  let Θ : X → PolarPoint → PolarPoint := fun x =>
    canonicalReferencePoint C K (z x) (m x) ∘ n07bMaterialRadiusChart T
  let B : X → PolarPoint → (PolarPoint →L[ℝ] PolarPoint) := fun x y =>
    fderiv ℝ (K.inverseChart (z x) (m x)) (Q x y)
  let A : X → PolarPoint → (PolarPoint →L[ℝ] PolarPoint) := fun x y =>
    fderiv ℝ (K.chart (C.referenceState, 0) (m x)) (Θ x y)
  have hphysical (x : X) : ContDiffAt ℝ ∞ (K.chart (z x) (m x))
      (n07bMaterialRadiusChart T (p x)) :=
    (hgeom.charts (z x) (hz x) (hs x) (m x)).2.2.2.2.1.contDiffAt
      ((hgeom.domains (z x) (hz x) (hs x) (m x)).1.mem_nhds (hp x))
  have hQmem (x : X) : Q x (p x) ∈ canonicalOpen S K (m x) :=
    (hgeom.charts (z x) (hz x) (hs x) (m x)).1 (hp x)
  have hQ (x : X) : ContDiffAt ℝ ∞ (Q x) (p x) :=
    (hphysical x).comp (p x) hR.contDiffAt
  have hΘmem (x : X) : Θ x (p x) ∈ physicalPieceOpen S K (C.referenceState, 0) (m x) :=
    (hgeom.charts (C.referenceState, 0) href hsref (m x)).2.1 (hQmem x)
  have hΘ (x : X) : ContDiffAt ℝ ∞ (Θ x) (p x) :=
    ((n07b_canonicalReferencePoint_contDiffOn hgeom href hsref (hz x) (hs x) (m x)).contDiffAt
      ((hgeom.domains (z x) (hz x) (hs x) (m x)).1.mem_nhds (hp x))).comp
        (p x) hR.contDiffAt
  have hB (x : X) : ContDiffAt ℝ ∞ (B x) (p x) :=
    (((hgeom.charts (z x) (hz x) (hs x) (m x)).2.2.2.2.2.1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hQmem x))).fderiv_right
        (m := ∞) (by simp)).comp (p x) (hQ x)
  have hA (x : X) : ContDiffAt ℝ ∞ (A x) (p x) :=
    (((hgeom.charts (C.referenceState, 0) href hsref (m x)).2.2.2.2.1.contDiffAt
      ((hgeom.domains (C.referenceState, 0) href hsref (m x)).1.mem_nhds (hΘmem x))).fderiv_right
        (m := ∞) (by simp)).comp (p x) (hΘ x)
  have hAe (e : PolarPoint) (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (fun y => A x y e) (p x)‖) :=
    n04Realization_envelope_clm_apply_jets hW p A (fun _ _ => e)
      hA (fun _ => contDiffAt_const) j
      (fun k hk => H.referenceDifferential k (by omega))
      (fun k _ => n04Realization_envelope_const_jets p (fun _ => e)
        (hasPositiveEnvelope_const W hW ‖e‖) k)
  have hreference (e : PolarPoint) (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (n07bReferenceDirection (canonicalCurrentPoint C K (z x) (m x))
          (canonicalReferencePoint C K (z x) (m x)) e ∘ n07bMaterialRadiusChart T) (p x)‖) := by
    have h := n04Realization_envelope_clm_apply_jets hW p B
      (fun x y => A x y e) hB (fun x => (hA x).clm_apply contDiffAt_const) j
      (fun k hk => H.inverseDifferential k (by omega)) (fun k hk => hAe e k (hk.trans hj))
    apply n04Realization_envelope_jets_congr p
      (fun x y => B x y (A x y e))
      (fun x => n07bReferenceDirection (canonicalCurrentPoint C K (z x) (m x))
        (canonicalReferencePoint C K (z x) (m x)) e ∘ n07bMaterialRadiusChart T) j h
    intro x
    filter_upwards [(n07bSourceMaterialPiece_isOpen hT hgeom (hz x) (hs x) (m x)).mem_nhds
      (hp x)] with y hy
    exact (n04Realization_referenceDirection_eqOn hgeom href hsref (hz x) (hs x) (m x) e hy).symm
  have hangular (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (canonicalPrimitiveDirection C K (z x) (m x) 0 ∘ n07bMaterialRadiusChart T) (p x)‖) := by
    have h := n04Realization_envelope_clm_apply_jets hW p B
      (fun _ _ => ((0, 1) : PolarPoint)) hB (fun _ => contDiffAt_const) j
      (fun k hk => H.inverseDifferential k (by omega))
      (fun k _ => n04Realization_envelope_const_jets p (fun _ => ((0, 1) : PolarPoint))
        (hasPositiveEnvelope_const W hW ‖((0, 1) : PolarPoint)‖) k)
    apply n04Realization_envelope_jets_congr p (fun x y => B x y (0, 1))
      (fun x => canonicalPrimitiveDirection C K (z x) (m x) 0 ∘ n07bMaterialRadiusChart T) j h
    intro x
    filter_upwards [(n07bSourceMaterialPiece_isOpen hT hgeom (hz x) (hs x) (m x)).mem_nhds
      (hp x)] with y hy
    exact (n04Realization_inverseAngleDirection_eqOn hgeom (hz x) (hs x) (m x) hy).symm
  have hYj (i : Fin 3) (j : ℕ) (hj : j ≤ N) : HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j
        (canonicalPrimitiveDirection C K (z x) (m x) i ∘ n07bMaterialRadiusChart T) (p x)‖) := by
    fin_cases i
    · exact hangular j hj
    · simpa only [← n07b_canonicalPrimitiveDirection_one C K] using hreference (1, 0) j hj
    · simpa only [← n07b_canonicalPrimitiveDirection_two C K] using hreference (0, 1) j hj
  have hYs (i : Fin 3) (x : X) : ContDiffAt ℝ ∞
      (canonicalPrimitiveDirection C K (z x) (m x) i) (n07bMaterialRadiusChart T (p x)) := by
    have hr (e : PolarPoint) :=
      (n07b_canonicalReferenceDirection_contDiffOn hgeom href hsref (hz x) (hs x) (m x) e).contDiffAt
        ((hgeom.domains (z x) (hz x) (hs x) (m x)).1.mem_nhds (hp x))
    fin_cases i
    · simpa only [← n07b_canonicalPrimitiveDirection_zero C K (z x) (m x)] using
        n07b_contDiffAt_inverseAngleVector (hphysical x)
          ((hgeom.charts (z x) (hz x) (hs x) (m x)).2.2.2.2.2.2.2 _ (hp x)).2.1
    · simpa only [← n07b_canonicalPrimitiveDirection_one C K (z x) (m x)] using hr (1, 0)
    · simpa only [← n07b_canonicalPrimitiveDirection_two C K (z x) (m x)] using hr (0, 1)
  intro i j k hk
  have h := n04Realization_materialDirection_envelopes hT hgeom hW z m p hz hs hp hE
    (fun x => canonicalPrimitiveDirection C K (z x) (m x) i) (hYs i) k
    (fun a ha => hYj i a (ha.trans hk))
    (fun a ha => H.density a (by omega)) (fun a ha => H.inverseDensity a (by omega))
  fin_cases j
  · apply n04Realization_envelope_jets_congr p
      (fun x => n07bMaterialDirectionV1 T (canonicalPrimitiveDirection C K (z x) (m x) i))
      (fun x => canonicalPrimitiveField D T C K (z x) (m x) (.inl (i, 0)) ∘
        n07bMaterialRadiusChart T) k h.1
    intro x
    exact Eventually.of_forall (fun y =>
      (n07b_canonicalPrimitiveField_direction D T C K (z x) (m x) i y).1.symm)
  · apply n04Realization_envelope_jets_congr p
      (fun x => n07bMaterialDirectionV2 T (canonicalPrimitiveDirection C K (z x) (m x) i))
      (fun x => canonicalPrimitiveField D T C K (z x) (m x) (.inl (i, 1)) ∘
        n07bMaterialRadiusChart T) k h.2.1
    intro x
    exact Eventually.of_forall (fun y =>
      (n07b_canonicalPrimitiveField_direction D T C K (z x) (m x) i y).2.1.symm)
  · apply n04Realization_envelope_jets_congr p
      (fun x => n07bMaterialDirectionDrift T K (z x) (m x)
        (canonicalPrimitiveDirection C K (z x) (m x) i))
      (fun x => canonicalPrimitiveField D T C K (z x) (m x) (.inl (i, 2)) ∘
        n07bMaterialRadiusChart T) k h.2.2
    intro x
    exact Eventually.of_forall (fun y =>
      (n07b_canonicalPrimitiveField_direction D T C K (z x) (m x) i y).2.2.symm)

end ContinuousFlexibility.Analysis
