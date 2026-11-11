import ContinuousFlexibility.Analysis.SolveStateSpaces

/-!
# The actual continuous projection onto the nonlinear state sector

The projection keeps the height and scalar profile coordinates, takes the
angular mean of the control coordinate, and takes the odd part of the chart
coordinate. Its decoded formulas identify the physical scalar residual even
away from the sector, including directions with arbitrary circle controls.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped Topology NNReal

set_option backward.isDefEq.respectTransparency false

section ProjectionAlgebra

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

private theorem n08_productProjection_existsTame
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) (hq : Monotone q) (mean odd : F →L[ℝ] F)
    (hm : IsTameLinear q q mean.toLinearMap 0 0)
    (ho : ∃ loss base, IsTameLinear q q odd.toLinearMap loss base) :
    ∃ loss base, IsTameLinear
      (pairGrading p (pairGrading realGrading (pairGrading q q)))
      (pairGrading p (pairGrading realGrading (pairGrading q q)))
      ((ContinuousLinearMap.id ℝ E).prodMap
        ((ContinuousLinearMap.id ℝ ℝ).prodMap (mean.prodMap odd))).toLinearMap loss base := by
  obtain ⟨loss, base, ho⟩ := ho
  have hr : Monotone realGrading := fun _ _ _ _ => le_rfl
  have hpair := solve_isTameLinear_prodMap hq hq hm ho
  have hrest := solve_isTameLinear_prodMap hr (pairGrading_monotone hq hq)
    (IsTameLinear.id realGrading) hpair
  have hfull := solve_isTameLinear_prodMap hp
    (pairGrading_monotone hr (pairGrading_monotone hq hq)) (IsTameLinear.id p) hrest
  refine ⟨loss, base, ?_⟩
  simpa only [ContinuousLinearMap.coe_prodMap, ContinuousLinearMap.coe_id,
    Nat.zero_max] using hfull

private theorem n08_codRestrict_existsTame
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (W : Submodule ℝ F) (L : E →L[ℝ] F) (hmem : ∀ x, L x ∈ W)
    (h : ∃ loss base, IsTameLinear p q L.toLinearMap loss base) :
    ∃ loss base, IsTameLinear p (fun n => (q n).comp W.subtype)
      (L.codRestrict W hmem).toLinearMap loss base := by
  obtain ⟨loss, base, ht⟩ := h
  exact ⟨loss, base, ht⟩

end ProjectionAlgebra

private theorem n08_oddFormula_odd {f g : ℝ → ℝ}
    (hg : ∀ θ, g θ = (f θ - f (-θ)) / 2) (θ : ℝ) : g (-θ) = -g θ := by
  rw [hg, hg, neg_neg]
  ring

private theorem n08_mean_projection_preserves_mean {E : Type*}
    (decode : E → ℕ → ℝ → ℝ) (M : E → E)
    (hm : ∀ u m θ, decode (M u) m θ = angularMean (decode u m)) (u : E) (m : ℕ) :
    angularMean (decode (M u) m) = angularMean (decode u m) := by
  have he : decode (M u) m = fun _ => angularMean (decode u m) := funext (hm u m)
  rw [he, angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_div]
  exact inv_mul_cancel_left₀ Real.pi_ne_zero _

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The actual odd projection supplied by the physical circle model. -/
def n08_oddCircleProjection (hS : IsPhysicalSpaces D T S) :
    CircleSpace S →L[ℝ] CircleSpace S :=
  (solve_parityProjection_data hS (3 / 4 : ℝ)).choose_spec.choose

theorem n08_oddCircleProjection_decode (hS : IsPhysicalSpaces D T S)
    (u : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (n08_oddCircleProjection hS u) m θ =
      ((S.circle (3 / 4 : ℝ)).decode u m θ -
        (S.circle (3 / 4 : ℝ)).decode u m (-θ)) / 2 :=
  (solve_parityProjection_data hS (3 / 4 : ℝ)).choose_spec.choose_spec.2.1 u m θ

theorem n08_oddCircleProjection_isTame (hS : IsPhysicalSpaces D T S) :
    ∃ loss base, IsTameLinear (S.circle (3 / 4 : ℝ)).grading
      (S.circle (3 / 4 : ℝ)).grading (n08_oddCircleProjection hS).toLinearMap loss base :=
  (solve_parityProjection_data hS (3 / 4 : ℝ)).choose_spec.choose_spec.2.2.2.2

theorem n08_oddCircleProjection_odd (hS : IsPhysicalSpaces D T S)
    (u : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (n08_oddCircleProjection hS u) m (-θ) =
      -(S.circle (3 / 4 : ℝ)).decode (n08_oddCircleProjection hS u) m θ :=
  n08_oddFormula_odd (n08_oddCircleProjection_decode hS u m) θ

theorem n08_oddCircleProjection_eq_self (hS : IsPhysicalSpaces D T S)
    (u : CircleSpace S)
    (hu : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode u m (-θ) =
      -(S.circle (3 / 4 : ℝ)).decode u m θ) :
    n08_oddCircleProjection hS u = u := by
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext m θ
  rw [n08_oddCircleProjection_decode, hu]
  ring

/-- Projection onto constant controls and odd chart perturbations. -/
def n08_stateProjection (hS : IsPhysicalSpaces D T S) :
    AnnularState S →L[ℝ] AnnularState S :=
  (ContinuousLinearMap.id ℝ (HeightPair S)).prodMap
    ((ContinuousLinearMap.id ℝ ℝ).prodMap
      ((circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ))).prodMap
        (n08_oddCircleProjection hS)))

theorem n08_stateProjection_apply (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    n08_stateProjection hS x = (x.1, x.2.1,
      circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1,
      n08_oddCircleProjection hS x.2.2.2) := rfl

theorem n08_stateProjection_height (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    (n08_stateProjection hS x).1 = x.1 := rfl

theorem n08_stateProjection_nu (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    (n08_stateProjection hS x).2.1 = x.2.1 := rfl

theorem n08_stateProjection_kappa_decode (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (n08_stateProjection hS x).2.2.1 m θ =
      stateKappa S x m :=
  circleAngularMeanProjection_decode (hS.2.1 (3 / 4 : ℝ)) x.2.2.1 m θ

theorem n08_stateProjection_chart_decode (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (n08_stateProjection hS x).2.2.2 m θ =
      ((S.circle (3 / 4 : ℝ)).decode x.2.2.2 m θ -
        (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m (-θ)) / 2 :=
  n08_oddCircleProjection_decode hS x.2.2.2 m θ

theorem n08_stateProjection_mem (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    n08_stateProjection hS x ∈ stateSectorSubmodule S := by
  constructor
  · intro m θ φ
    exact circleAngularMeanProjection_constant (hS.2.1 (3 / 4 : ℝ)) x.2.2.1 m θ φ
  · intro m θ
    exact n08_oddCircleProjection_odd hS x.2.2.2 m θ

theorem n08_stateProjection_eq_self (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (hx : x ∈ stateSectorSubmodule S) :
    n08_stateProjection hS x = x := by
  rw [n08_stateProjection_apply]
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext
    (circleAngularMeanProjection_eq_self (hS.2.1 (3 / 4 : ℝ)) x.2.2.1 hx.1)
    (n08_oddCircleProjection_eq_self hS x.2.2.2 hx.2)))

theorem n08_stateProjection_idempotent (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) :
    n08_stateProjection hS (n08_stateProjection hS x) = n08_stateProjection hS x :=
  n08_stateProjection_eq_self hS _ (n08_stateProjection_mem hS x)

theorem n08_stateProjection_eq_self_iff (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) :
    n08_stateProjection hS x = x ↔ x ∈ stateSectorSubmodule S := by
  constructor
  · intro hx
    exact hx ▸ n08_stateProjection_mem hS x
  · exact n08_stateProjection_eq_self hS x

/-- The sector is the equalizer of a continuous projection and the identity. -/
theorem n08_isClosed_stateSector (hS : IsPhysicalSpaces D T S) :
    IsClosed (stateSectorSubmodule S : Set (AnnularState S)) := by
  have hset : (stateSectorSubmodule S : Set (AnnularState S)) =
      {x | n08_stateProjection hS x = x} := by
    ext x
    exact (n08_stateProjection_eq_self_iff hS x).symm
  rw [hset]
  exact isClosed_eq (n08_stateProjection hS).continuous continuous_id

theorem n08_stateProjection_isTame (hS : IsPhysicalSpaces D T S) :
    ∃ loss base, IsTameLinear (stateGrading S) (stateGrading S)
      (n08_stateProjection hS).toLinearMap loss base :=
  n08_productProjection_existsTame
    (p := heightPairGrading S) (q := (S.circle (3 / 4 : ℝ)).grading)
    (pairGrading_monotone (gradedSeminorm_monotone _ _) (fun _ _ _ _ => le_rfl))
    (gradedSeminorm_monotone _ _)
    (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ))) (n08_oddCircleProjection hS)
    (circleAngularMeanProjection_isTame (hS.2.1 (3 / 4 : ℝ)))
    (n08_oddCircleProjection_isTame hS)

/-- The same projection with codomain the actual closed sector. -/
def n08_sectorProjection (hS : IsPhysicalSpaces D T S) :
    AnnularState S →L[ℝ] StateDirections S :=
  (n08_stateProjection hS).codRestrict (stateSectorSubmodule S) (n08_stateProjection_mem hS)

theorem n08_sectorProjection_val (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    (n08_sectorProjection hS x).val = n08_stateProjection hS x := rfl

theorem n08_sectorProjection_subtype (hS : IsPhysicalSpaces D T S)
    (x : StateDirections S) : n08_sectorProjection hS x.val = x :=
  Subtype.ext (n08_stateProjection_eq_self hS x.val x.property)

theorem n08_sectorProjection_isTame (hS : IsPhysicalSpaces D T S) :
    ∃ loss base, IsTameLinear (stateGrading S) (sectorGrading S)
      (n08_sectorProjection hS).toLinearMap loss base :=
  n08_codRestrict_existsTame (p := stateGrading S) (q := stateGrading S)
    (stateSectorSubmodule S) (n08_stateProjection hS)
    (n08_stateProjection_mem hS) (n08_stateProjection_isTame hS)

theorem n08_stateProjection_reference (hS : IsPhysicalSpaces D T S)
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C) :
    n08_stateProjection hS C.referenceState = C.referenceState := by
  apply n08_stateProjection_eq_self hS
  obtain ⟨_, _, _, hκ, hh, _⟩ := href
  constructor
  · intro m θ φ
    simp only [hκ, map_zero, Pi.zero_apply]
  · intro m θ
    simp only [hh, map_zero, Pi.zero_apply, neg_zero]

/-- An arbitrary control direction becomes exactly its angular mean. -/
theorem n08_stateProjection_kappaDirection (hS : IsPhysicalSpaces D T S)
    (u : CircleSpace S) :
    n08_stateProjection hS (0, 0, u, 0) =
      (0, 0, circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ)) u, 0) :=
  (n08_stateProjection_apply hS _).trans
    (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (map_zero (n08_oddCircleProjection hS)))))

theorem n08_stateProjection_nuDirection (hS : IsPhysicalSpaces D T S) (a : ℝ) :
    n08_stateProjection hS (0, a, 0, 0) = (0, a, 0, 0) :=
  (n08_stateProjection_apply hS _).trans
    (Prod.ext rfl (Prod.ext rfl (Prod.ext
      (map_zero (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ))))
      (map_zero (n08_oddCircleProjection hS)))))

theorem n08_stateProjection_heightDirection (hS : IsPhysicalSpaces D T S)
    (u : HeightPair S) : n08_stateProjection hS (u, 0, 0, 0) = (u, 0, 0, 0) :=
  (n08_stateProjection_apply hS _).trans
    (Prod.ext rfl (Prod.ext rfl (Prod.ext
      (map_zero (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ))))
      (map_zero (n08_oddCircleProjection hS)))))

theorem n08_stateU_projection (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    stateU S (n08_stateProjection hS x) = stateU S x := rfl

theorem n08_stateKappa_projection (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) :
    stateKappa S (n08_stateProjection hS x) m = stateKappa S x m :=
  n08_mean_projection_preserves_mean (S.circle (3 / 4 : ℝ)).decode
    (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ)))
    (circleAngularMeanProjection_decode (hS.2.1 (3 / 4 : ℝ))) x.2.2.1 m

theorem n08_stateProfile_projection (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (x : AnnularState S) :
    stateProfile D S C (n08_stateProjection hS x) = stateProfile D S C x := by
  funext r
  simp only [stateProfile, n08_stateProjection_nu, n08_stateKappa_projection]

theorem n08_stateRadialHeight_projection (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (x : AnnularState S) :
    stateRadialHeight D S C (n08_stateProjection hS x) = stateRadialHeight D S C x := by
  funext r
  simp only [stateRadialHeight, n08_stateProfile_projection]

theorem n08_stateHeight_projection (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) :
    stateHeight D S C (n08_stateProjection hS z.1, z.2) = stateHeight D S C z := by
  funext p
  simp only [stateHeight, n08_stateRadialHeight_projection, n08_stateU_projection]

/-- Projection preserves the actual scalar expression on all states, so its
off-sector extension has the same scalar and arbitrary control derivatives. -/
theorem n08_scalarResidualField_projection (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) :
    scalarResidualField D S C (n08_stateProjection hS z.1, z.2) =
      scalarResidualField D S C z := by
  funext p
  simp only [scalarResidualField, n08_stateProfile_projection,
    n08_stateRadialHeight_projection, n08_stateU_projection]

end ContinuousFlexibility.Statements
