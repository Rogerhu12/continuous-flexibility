module

public import ContinuousFlexibility.Analysis.SolveStateSpaces
public import ContinuousFlexibility.Analysis.N06Neighborhood
public import ContinuousFlexibility.Analysis.StateKappaBounds
public import ContinuousFlexibility.Analysis.TameElementaryCalculus
public import ContinuousFlexibility.Analysis.TameTransfer
public import ContinuousFlexibility.Analysis.N01cBoundsRestriction
public import ContinuousFlexibility.Analysis.N06Neighborhood

/-!
# Restricting the cumulative nonlinear construction

The control Neumann estimate chooses a stronger finite input order and a
smaller positive radius. Every property through N08 survives that choice,
with the same geometric data, inverse data, and loss. In particular the
one-high-factor estimates retain their common neighborhood at every order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base base' loss : ℕ} {ε ε' : ℝ}

theorem coupled_stateNeighborhood_isOpen (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    IsOpen (stateNeighborhood S C base ε) :=
  (isOpen_lt (((solve_stateGrading_withSeminorms S).continuous_seminorm base).comp
    (continuous_fst.sub continuous_const)) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

theorem coupled_sectorNeighborhood_isOpen (S : PhysicalSpacesData)
    (base : ℕ) (ε q0 : ℝ) : IsOpen (sectorNeighborhood S base ε q0) :=
  (isOpen_lt (((solve_sectorGrading_withSeminorms S).continuous_seminorm base).comp
    continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

theorem coupled_stateNeighborhood_mono (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨lt_of_le_of_lt (solve_stateGrading_monotone S hb _) (hz.1.trans_le hε),
    hz.2.trans_le hε⟩

theorem coupled_sectorNeighborhood_mono {q0 q0' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) (hq : q0' ≤ q0) :
    sectorNeighborhood S base' ε' q0' ⊆ sectorNeighborhood S base ε q0 := by
  intro z hz
  exact ⟨lt_of_le_of_lt (solve_sectorGrading_monotone S hb _) (hz.1.trans_le hε),
    hz.2.trans_le hq⟩

private theorem coupled_linearFamilyTame_mono
    {E F G : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U V : Set E} {A : E → G →ₗ[ℝ] F}
    (h : LinearFamilyTame p q r U A) (hVU : V ⊆ U) :
    LinearFamilyTame p q r V A := by
  obtain ⟨l, b, h⟩ := h
  refine ⟨l, b, fun s hs => ?_⟩
  obtain ⟨c, hc, h⟩ := h s hs
  exact ⟨c, hc, fun z hz => h z (hVU hz)⟩

private theorem coupled_oneHighVariationWeight_mono
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {b b' high : ℕ}
    (hb : b ≤ b') (x : E) {k : ℕ} (v : Fin k → E) :
    oneHighVariationWeight p b high x v ≤ oneHighVariationWeight p b' high x v := by
  simpa only [oneHighVariationWeight, tameJetSize, Nat.add_zero] using
    (tameJetSize_mono hp (loss := 0) (loss' := 0) le_rfl hb k high x v)

private theorem coupled_forall_mem_mono {X : Type*} {U V : Set X}
    (hVU : V ⊆ U) {P : X → Prop} (h : ∀ x ∈ U, P x) : ∀ x ∈ V, P x :=
  fun x hx => h x (hVU hx)

private theorem coupled_orderedBounds_mono {X : Type*} {U V : Set X}
    (hVU : V ⊆ U) {P : ℕ → ℝ → X → Prop}
    (h : ∀ s : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ U, P s c x) :
    ∀ s : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ V, P s c x := by
  intro s
  obtain ⟨c, hc, h⟩ := h s
  exact ⟨c, hc, coupled_forall_mem_mono hVU h⟩

private theorem coupled_weightedTower_restrict
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {U V : Set E} (hV : IsOpen V) (hVU : V ⊆ U)
    {base base' high k : ℕ} (hb : base ≤ base') (x0 : E)
    {f : E → ℝ} (φ : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∃ J : SmoothDirections U f, ∀ z ∈ U, ∀ v : Fin k → E,
      φ (J.D k z v) ≤ a * oneHighVariationWeight p base high (z - x0) v) :
    ∃ J : SmoothDirections V f, ∀ z ∈ V, ∀ v : Fin k → E,
      φ (J.D k z v) ≤ a * oneHighVariationWeight p base' high (z - x0) v := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨smoothDirectionsRestrict J hV hVU, fun z hz v => ?_⟩
  exact (hJ z (hVU hz) v).trans
    (mul_le_mul_of_nonneg_left (coupled_oneHighVariationWeight_mono hp hb _ v) ha)

private theorem coupled_coefficientBounds_restrict
    (hp : Monotone (pairGrading (stateGrading S) realGrading))
    (hopen : IsOpen (stateNeighborhood S C base' ε'))
    (hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε)
    (hb : base ≤ base')
    (hpos : ∀ m, 0 ≤ T.H (T.sample m) ∧ 0 ≤ T.E0 (T.sample m))
    (hCoef : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b p,
      a + b ≤ s → p.1 ∈ D.cells m →
      ∃ J : SmoothDirections (stateNeighborhood S C base ε)
        (coefficientFamily D S C i a b p),
        ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
          |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample m) ^ B *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base (s + loss) (z - (C.referenceState, 0)) v) :
    ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b p,
      a + b ≤ s → p.1 ∈ D.cells m →
      ∃ J : SmoothDirections (stateNeighborhood S C base' ε')
        (coefficientFamily D S C i a b p),
        ∀ z ∈ stateNeighborhood S C base' ε', ∀ v : Fin k → (AnnularState S × ℝ),
          |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample m) ^ B *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base' (s + loss) (z - (C.referenceState, 0)) v := by
  intro k s
  let c : ℝ := (hCoef k s).choose
  have hc : 0 < c := (hCoef k s).choose_spec.1
  refine ⟨c, hc, fun m i a b p hab hpm => ?_⟩
  exact coupled_weightedTower_restrict hp hopen hsub hb (C.referenceState, 0) abs
    (mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg (hpos m).1 _))
      (Real.rpow_nonneg (hpos m).2 _)) ((hCoef k s).choose_spec.2 m i a b p hab hpm)

private theorem coupled_flowBounds_restrict
    (hp : Monotone (pairGrading (stateGrading S) realGrading))
    (hopen : IsOpen (stateNeighborhood S C base' ε'))
    (hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε)
    (hb : base ≤ base')
    (hpos : ∀ m, 0 ≤ T.H (T.sample m) ∧ 0 ≤ T.E0 (T.sample m))
    (hFlow : OrdinaryFlowFamilyTameBounds T S C base loss ε) :
    OrdinaryFlowFamilyTameBounds T S C base' loss ε' := by
  exact ordinaryFlowBounds_restrict
    (E := AnnularState S × ℝ)
    (U := stateNeighborhood S C base ε) (V := stateNeighborhood S C base' ε')
    (grading := pairGrading (stateGrading S) realGrading)
    (center := (C.referenceState, 0)) (family := ordinaryFlowFamily S C)
    (left := C.left) (right := C.right)
    (weight := fun B m => B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B)
    hopen hsub hp hb (le_refl loss)
    (fun B hB m => mul_nonneg
      (mul_nonneg hB.le (Real.rpow_nonneg (hpos (C.cell m)).1 _))
      (Real.rpow_nonneg (hpos (C.cell m)).2 _)) hFlow

theorem coupled_N01Properties_restrict (hT : IsMaterialData D T)
    (h : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) (hε' : 0 < ε') :
    N01Properties D T S C base' loss ε' := by
  have hsub := coupled_stateNeighborhood_mono (S := S) (C := C) hb hε
  have hopen := coupled_stateNeighborhood_isOpen S C base' ε'
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    pairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  have hpos (m : ℕ) : 0 ≤ T.H (T.sample m) ∧ 0 ≤ T.E0 (T.sample m) := by
    have hm := hT.2.1 _ (materialSample_mem_radialCore hT h.1.1.choose_spec.2.1 m)
    exact ⟨hm.2.1.le, hm.2.2.1.le⟩
  refine And.imp id ?_ h
  refine And.imp (fun _ => hε') ?_
  refine And.imp id ?_
  refine And.imp id ?_
  refine And.imp id ?_
  refine And.imp id ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  exact And.imp (coupled_coefficientBounds_restrict hp hopen hsub hb hpos)
    (coupled_flowBounds_restrict hp hopen hsub hb hpos)

theorem coupled_N02Properties_restrict (h : N02Properties D T S C R base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) : N02Properties D T S C R base' ε' := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩
  have hsub := coupled_stateNeighborhood_mono (S := S) (C := C) hb hε
  exact ⟨(fun z hz => h₁ z (hsub hz)), (fun z hz => h₂ z (hsub hz)),
    (fun z hz => h₃ z (hsub hz)), h₄, (fun z hz => h₅ z (hsub hz)),
    (fun z hz => h₆ z (hsub hz)), (fun z hz => h₇ z (hsub hz)), h₈, h₉, h₁₀,
    smoothTameOn_mono h₁₁ (coupled_sectorNeighborhood_isOpen S base' ε' ε')
      (coupled_sectorNeighborhood_mono hb hε hε)⟩

theorem coupled_N03Properties_restrict (h : N03Properties D T S C R L base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) : N03Properties D T S C R L base' ε' :=
  n06_N03Properties_mono h hb hε

theorem coupled_N04Properties_restrict (h : N04Properties D T S C L K base loss ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) : N04Properties D T S C L K base' loss ε' :=
  n06_N04Properties_mono h hb hε

variable {Vol : VolumeModelData S K} {b : ℕ}
  {Domain : CanonicalDomainData S K Vol b}
  {Relative : RelativeInverseData S K Vol b Domain}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}

theorem coupled_N06Properties_restrict
    (h : N06Properties D S C K L Vol b Domain Relative base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) (hε' : 0 < ε') :
    N06Properties D S C K L Vol b Domain Relative base' ε' :=
  ⟨hε', fun z hz => h.2 z (coupled_stateNeighborhood_mono hb hε hz)⟩

theorem coupled_scalarInverseProperties_restrict
    (h : ScalarInverseProperties D S C L G base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    ScalarInverseProperties D S C L G base' ε' := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  have hsub := coupled_stateNeighborhood_mono (S := S) (C := C) hb hε
  have hss := coupled_sectorNeighborhood_mono (S := S) hb hε hε
  exact ⟨(fun z hz => h₁ z (hsub hz)), (fun z hz => h₂ z (hsub hz)),
    coupled_linearFamilyTame_mono h₃ hss, smoothTameOn_mono h₄
      ((coupled_sectorNeighborhood_isOpen S base' ε' ε').prod isOpen_univ)
      (Set.prod_mono hss (subset_refl _))⟩

theorem coupled_scalarBanachBridgeProperties_restrict
    (h : ScalarBanachBridgeProperties D S C K Vol b Domain Relative G base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    ScalarBanachBridgeProperties D S C K Vol b Domain Relative G base' ε' := by
  obtain ⟨s, hs, c, hc, h⟩ := h
  exact ⟨s, hs, c, hc, fun z hz => h z (coupled_stateNeighborhood_mono hb hε hz)⟩

theorem coupled_N08Properties_restrict
    (h : N08Properties D T S C R G P B base loss ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N08Properties D T S C R G P B base' loss ε' := by
  have hsub := coupled_stateNeighborhood_mono (S := S) (C := C) hb hε
  have hss := coupled_sectorNeighborhood_mono (S := S) hb hε hε
  have hopen := coupled_sectorNeighborhood_isOpen S base' ε' ε'
  refine And.imp id ?_ h
  refine And.imp (fun _ => hopen) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp id ?_
  refine And.imp id ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp id ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_orderedBounds_mono hsub) ?_
  exact And.imp (fun h => smoothTameOn_mono h hopen hss)
    (fun h => smoothTameOn_mono h (hopen.prod isOpen_univ)
      (Set.prod_mono hss (subset_refl _)))

/-- One stronger input order and one smaller radius retain every property
of the construction through the actual N08 residual and control columns. -/
theorem coupled_nonlinearPropertiesThrough08_restrict (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough08 D T S C R L K Vol b Domain Relative G P B
      base loss ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) (hε' : 0 < ε') :
    NonlinearPropertiesThrough08 D T S C R L K Vol b Domain Relative G P B
      base' loss ε' := by
  rcases h with ⟨h7, h8⟩
  rcases h7 with ⟨h6, hG, hBridge⟩
  rcases h6 with ⟨h5, h6⟩
  have h5' := n06_NonlinearPropertiesThrough05_mono hT h5 hb hε' hε
  have h6' := coupled_N06Properties_restrict h6 hb hε hε'
  have hG' := coupled_scalarInverseProperties_restrict hG hb hε
  have hBridge' := coupled_scalarBanachBridgeProperties_restrict hBridge hb hε
  have h8' := coupled_N08Properties_restrict h8 hb hε
  exact ⟨⟨⟨h5', h6'⟩, hG', hBridge'⟩, h8'⟩

theorem coupled_neighborhood_mono {q0 q0' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) (hq : q0' ≤ q0) :
    coupledNeighborhood S C base' ε' q0' ⊆ coupledNeighborhood S C base ε q0 := by
  intro z hz
  exact ⟨lt_of_le_of_lt (solve_stateGrading_monotone S hb _) (hz.1.trans_le hε),
    hz.2.trans_le hq⟩

/-- The already constructed inverse remains the same map when a later
error estimate requires a smaller common neighborhood. -/
theorem coupled_N09Properties_restrict
    {N : ControlInverseData S} {V : CoupledInverseData S} {q0 q0' : ℝ}
    (h : N09Properties D T S C R G B N V base ε q0)
    (hb : base ≤ base') (hε : ε' ≤ ε) (hq : q0' ≤ q0)
    (hq0' : 0 < q0') (hqε' : q0' ≤ ε') :
    N09Properties D T S C R G B N V base' ε' q0' := by
  have hsub := coupled_neighborhood_mono (S := S) (C := C) hb hε hq
  have hss := coupled_sectorNeighborhood_mono (S := S) hb hε hq
  refine And.imp (fun _ => hq0') ?_ h
  refine And.imp (fun _ => hqε') ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  refine And.imp (coupled_forall_mem_mono hsub) ?_
  exact And.imp (coupled_forall_mem_mono hss)
    (fun h => smoothTameOn_mono h
      ((coupled_sectorNeighborhood_isOpen S base' ε' q0').prod isOpen_univ)
      (Set.prod_mono hss (subset_refl _)))

theorem coupled_nonlinearPropertiesThrough09_restrict
    {N : ControlInverseData S} {V : CoupledInverseData S} {q0 q0' : ℝ}
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough09 D T S C R L K Vol b Domain Relative G P B N V
      base loss ε q0)
    (hb : base ≤ base') (hε : ε' ≤ ε) (hε' : 0 < ε')
    (hq : q0' ≤ q0) (hq0' : 0 < q0') (hqε' : q0' ≤ ε') :
    NonlinearPropertiesThrough09 D T S C R L K Vol b Domain Relative G P B N V
      base' loss ε' q0' :=
  ⟨coupled_nonlinearPropertiesThrough08_restrict hT h.1 hb hε hε',
    coupled_N09Properties_restrict h.2 hb hε hq hq0' hqε'⟩

end ContinuousFlexibility.Statements
