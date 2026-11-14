module

public import ContinuousFlexibility.Analysis.N04PrincipalAllPairs

/-!
# Height and inverse height on one common sector

The geometric current data supplies the actual pulled height on every
piece. Its reference jets and the reference inverse-height atom allow
the reciprocal calculus to choose a single smaller sector before any
spatial or parameter orders are selected.
-/

@[expose] public section

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

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04PrincipalNegative_height_pairBounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (fun _ => True) b ε) :
    G.n04PrincipalPair η b ε (G.pulledHeight η) (G.pulledHeightRef η) := by
  have hreference := G.n04PrincipalPositive_pulledHeightRef_jets h η href
  have hheight := G.n04PrincipalPositive_sample_height_bound η
  have hreferenceBound : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m, True → ∀ q : unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (G.pulledHeightRef η m) q.val| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
    intro s
    have hb := hreference.2 s
    exact ⟨hb.choose, hb.choose_spec.1, fun m _ q i j hij =>
      hb.choose_spec.2 m false q i j hij⟩
  have hp := hg.2.n04Principal_pairBounds (fun m _ => hreference.1 m false)
    hreferenceBound (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1
    hheight.choose_spec.1.le hheight.choose_spec.2
  exact hp.reindex (fun m : ℕ => (⟨m, trivial⟩ : {m : ℕ // True}))

/-- Both reciprocal and original height are controlled on the same
smaller sector, with the radius and low order preceding all jet orders. -/
theorem n04PrincipalNegative_height_inverse_pairs {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (fun _ => True) b ε) :
    ∃ b' : ℕ, b ≤ b' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 / 2 ∧
      G.n04PrincipalPair η b' ε' (G.pulledHeight η) (G.pulledHeightRef η) ∧
      G.n04PrincipalPair η b' ε'
        (fun z m q => (G.pulledHeight η z m q)⁻¹)
        (fun m q => (G.pulledHeightRef η m q)⁻¹) := by
  have hp := G.n04PrincipalNegative_height_pairBounds h η href hg
  have hD : IsAccumulatingProfile G.W.D := G.W.radial.1
  have hT : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  have hzero : ∀ m, EqOn (G.pulledHeight η 0 m) (G.pulledHeightRef η m) unitStrip := by
    intro m q _
    unfold pulledHeight pulledHeightRef
    rw [G.n04PrincipalPositive_lift_zero η]
  have hA := (G.n04PrincipalPositive_admissible_parts h η).1
  have hr := G.n04PrincipalPositive_reference_pulledHeight_bounds h η href
  have hreference : ∃ R : ℝ, 0 < R ∧ ∀ m q, q ∈ unitStrip →
      G.pulledHeightRef η m q ≠ 0 ∧ |(G.pulledHeightRef η m q)⁻¹| ≤
        R * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ R := by
    refine ⟨hr.choose, hr.choose_spec.1, ?_⟩
    intro m q hq
    have hq' := n04PrincipalNegative_unitPoint_mem (G.V η) m
      (hA.referenceBounds m).2.1 hq
    have hh := hr.choose_spec.2 m (canonicalUnitPoint (G.V η) m q) hq'
    exact ⟨hh.1.ne', hh.2.2⟩
  have hi := hp.inverse_neighborhood
    hD hT h.2.1 (G.n04PrincipalPositive_parameter_interpolation η)
    (G.cost_nonneg η).2.2 hzero hreference
  let b' : ℕ := hi.choose
  have hbb' : b ≤ b' := hi.choose_spec.1
  let ε' : ℝ := hi.choose_spec.2.choose
  have hε' : 0 < ε' := hi.choose_spec.2.choose_spec.1
  have hε'ε : ε' ≤ ε := hi.choose_spec.2.choose_spec.2.1
  have hε'half : ε' ≤ 1 / 2 := hi.choose_spec.2.choose_spec.2.2.1
  have hQ := hi.choose_spec.2.choose_spec.2.2.2
  refine ⟨b', hbb', ε', hε', hε'ε, hε'half, ?_, hQ⟩
  exact hp.restrict (isOpen_sectorNeighborhood (G.S η) b' ε' ε')
    (sectorNeighborhood_mono (G.S η) hbb' hε'ε hε'ε)

/-- The reciprocal-height sector also supports the actual negative
potential and its reference as one paired family. -/
theorem n04PrincipalNegative_potential_pair_neighborhood {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (fun _ => True) b ε) :
    ∃ b' : ℕ, b ≤ b' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 / 2 ∧
      G.n04PrincipalPair η b' ε' (G.pulledHeight η) (G.pulledHeightRef η) ∧
      G.n04PrincipalPair η b' ε'
        (fun z m q => (G.pulledHeight η z m q)⁻¹)
        (fun m q => (G.pulledHeightRef η m q)⁻¹) ∧
      G.n04PrincipalNegativePairBounds η b' ε'
        (G.atomFamily η .potential) (G.atomRef η .potential) := by
  have hi := G.n04PrincipalNegative_height_inverse_pairs h η href hg
  let b' : ℕ := hi.choose
  have hbb' : b ≤ b' := hi.choose_spec.1
  let ε' : ℝ := hi.choose_spec.2.choose
  have hε' : 0 < ε' := hi.choose_spec.2.choose_spec.1
  have hε'ε : ε' ≤ ε := hi.choose_spec.2.choose_spec.2.1
  have hε'half : ε' ≤ 1 / 2 := hi.choose_spec.2.choose_spec.2.2.1
  have hH := hi.choose_spec.2.choose_spec.2.2.2.1
  have hQ := hi.choose_spec.2.choose_spec.2.2.2.2
  refine ⟨b', hbb', ε', hε', hε'ε, hε'half, hH, hQ, ?_⟩
  exact G.n04PrincipalNegative_potential_pairBounds (G.admissible_mono h hbb' hε' hε'ε)
    η href (G.n04PrincipalPositive_parameter_interpolation η)
    (fun m _ => Real.rpow_pos_of_pos (G.n04PrincipalPositive_sample_height_pos η m) _)
    (hH.reindex (Subtype.val : {m : ℕ // G.Neg η m} → ℕ))
    (hQ.reindex (Subtype.val : {m : ℕ // G.Neg η m} → ℕ))

end N04RealizationGauge

end ContinuousFlexibility.Analysis
