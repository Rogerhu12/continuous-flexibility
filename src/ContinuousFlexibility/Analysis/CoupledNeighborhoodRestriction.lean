import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.StateKappaBounds
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Restricting the cumulative nonlinear construction

The control Neumann estimate chooses a stronger finite input order and a
smaller positive radius. Every property through N08 survives that choice,
with the same geometric data, inverse data, and loss. In particular the
one-high-factor estimates retain their common neighborhood at every order.
-/

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

theorem coupled_N01Properties_restrict (hT : IsMaterialData D T)
    (h : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) (hε' : 0 < ε') :
    N01Properties D T S C base' loss ε' := by
  have hD := h.1
  have hRef := h.2.2.1
  have hCtrl := h.2.2.2.1
  have hIdx := h.2.2.2.2.1
  have hJets := h.2.2.2.2.2.1
  have hFlow := h.2.2.2.2.2.2.1
  have hChart := h.2.2.2.2.2.2.2.1
  have hInv := h.2.2.2.2.2.2.2.2.1
  have hBounds := h.2.2.2.2.2.2.2.2.2.1
  have hZero := h.2.2.2.2.2.2.2.2.2.2.1
  have hCoef := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hFlowJet := h.2.2.2.2.2.2.2.2.2.2.2.2
  have hsub := coupled_stateNeighborhood_mono (S := S) (C := C) hb hε
  have hopen := coupled_stateNeighborhood_isOpen S C base' ε'
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    pairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  have hpos (m : ℕ) : 0 < T.H (T.sample m) ∧ 0 < T.E0 (T.sample m) := by
    have hm := hT.2.1 _ (materialSample_mem_radialCore hT hD.1.choose_spec.2.1 m)
    exact ⟨hm.2.1, hm.2.2.1⟩
  refine ⟨hD, hε', hRef, hCtrl, hIdx, hJets,
    (fun z hz => hFlow z (hsub hz)), (fun z hz => hChart z (hsub hz)),
    (fun z hz => hInv z (hsub hz)), (fun z hz => hBounds z (hsub hz)),
    (fun z hz => hZero z (hsub hz)), ?_, ?_⟩
  · intro k s
    obtain ⟨c, hc, h⟩ := hCoef k s
    refine ⟨c, hc, fun m i a b p hab hpm => ?_⟩
    obtain ⟨J, hJ⟩ := h m i a b p hab hpm
    refine ⟨smoothDirectionsRestrict J hopen hsub, fun z hz v => ?_⟩
    exact (hJ z (hsub hz) v).trans
      (mul_le_mul_of_nonneg_left (coupled_oneHighVariationWeight_mono hp hb _ v)
        (mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg (hpos m).1.le _))
          (Real.rpow_nonneg (hpos m).2.le _)))
  · intro k s
    obtain ⟨c, hc, h⟩ := hFlowJet k s
    refine ⟨c, hc, fun m a b p hab hpm => ?_⟩
    obtain ⟨J, hJ⟩ := h m a b p hab hpm
    refine ⟨smoothDirectionsRestrict J hopen hsub, fun z hz v => ?_⟩
    exact (hJ z (hsub hz) v).trans
      (mul_le_mul_of_nonneg_left (coupled_oneHighVariationWeight_mono hp hb _ v)
        (mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg (hpos (C.cell m)).1.le _))
          (Real.rpow_nonneg (hpos (C.cell m)).2.le _)))

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
    (hb : base ≤ base') (hε : ε' ≤ ε) : N03Properties D T S C R L base' ε' := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  have hsub := coupled_stateNeighborhood_mono (S := S) (C := C) hb hε
  exact ⟨(fun z hz => h₁ z (hsub hz)), (fun z hz => h₂ z (hsub hz)),
    (fun z hz => h₃ z (hsub hz)), (fun z hz => h₄ z (hsub hz)),
    (fun z hz => h₅ z (hsub hz)), (fun z hz => h₆ z (hsub hz)),
    (fun z hz => h₇ z (hsub hz)), smoothTameOn_mono h₈
      (((coupled_sectorNeighborhood_isOpen S base' ε' ε').prod isOpen_univ).prod
        isOpen_univ)
      (Set.prod_mono (Set.prod_mono (coupled_sectorNeighborhood_mono hb hε hε)
        (subset_refl _)) (subset_refl _))⟩

theorem coupled_N04Properties_restrict (h : N04Properties D T S C L K base loss ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) : N04Properties D T S C L K base' loss ε' := by
  have h₁ := h.1
  have h₂ := h.2.1
  have h₃ := h.2.2.1
  have h₄ := h.2.2.2.1
  have h₅ := h.2.2.2.2.1
  have h₆ := h.2.2.2.2.2.1
  have h₇ := h.2.2.2.2.2.2.1
  have h₈ := h.2.2.2.2.2.2.2.1
  have h₉ := h.2.2.2.2.2.2.2.2.1
  have h₁₀ := h.2.2.2.2.2.2.2.2.2.1
  have h₁₁ := h.2.2.2.2.2.2.2.2.2.2.1
  have h₁₂ := h.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₃ := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₄ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₅ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₆ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₇ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₈ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsub := coupled_stateNeighborhood_mono (S := S) (C := C) hb hε
  refine ⟨h₁, h₂, (fun z hz => h₃ z (hsub hz)), h₄, h₅, h₆, h₇,
    (fun z hz => h₈ z (hsub hz)), (fun z hz => h₉ z (hsub hz)),
    (fun z hz => h₁₀ z (hsub hz)), (fun z hz => h₁₁ z (hsub hz)), h₁₂,
    (fun z hz => h₁₃ z (hsub hz)), (fun z hz => h₁₄ z (hsub hz)),
    (fun z hz => h₁₅ z (hsub hz)), (fun z hz => h₁₆ z (hsub hz)), ?_,
    (fun z hz => h₁₈ z (hsub hz))⟩
  intro s
  obtain ⟨c, hc, h⟩ := h₁₇ s
  exact ⟨c, hc, fun z hz => h z (hsub hz)⟩

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
  have h₁ := h.1
  have h₃ := h.2.2.1
  have h₄ := h.2.2.2.1
  have h₅ := h.2.2.2.2.1
  have h₆ := h.2.2.2.2.2.1
  have h₇ := h.2.2.2.2.2.2.1
  have h₈ := h.2.2.2.2.2.2.2.1
  have h₉ := h.2.2.2.2.2.2.2.2.1
  have h₁₀ := h.2.2.2.2.2.2.2.2.2.1
  have h₁₁ := h.2.2.2.2.2.2.2.2.2.2.1
  have h₁₂ := h.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₃ := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₄ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₅ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₆ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₇ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₈ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h₁₉ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsub := coupled_stateNeighborhood_mono (S := S) (C := C) hb hε
  have hss := coupled_sectorNeighborhood_mono (S := S) hb hε hε
  have hopen := coupled_sectorNeighborhood_isOpen S base' ε' ε'
  refine ⟨h₁, hopen, (fun z hz => h₃ z (hsub hz)), (fun z hz => h₄ z (hsub hz)),
    h₅, h₆, (fun z hz => h₇ z (hsub hz)), (fun z hz => h₈ z (hsub hz)),
    (fun z hz => h₉ z (hsub hz)), (fun z hz => h₁₀ z (hsub hz)),
    (fun z hz => h₁₁ z (hsub hz)), (fun z hz => h₁₂ z (hsub hz)),
    (fun z hz => h₁₃ z (hsub hz)), h₁₄, (fun z hz => h₁₅ z (hsub hz)),
    (fun z hz => h₁₆ z (hsub hz)), ?_, smoothTameOn_mono h₁₈ hopen hss,
    smoothTameOn_mono h₁₉ (hopen.prod isOpen_univ)
      (Set.prod_mono hss (subset_refl _))⟩
  intro s
  obtain ⟨c, hc, h⟩ := h₁₇ s
  exact ⟨c, hc, fun z hz => h z (hsub hz)⟩

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
  rcases h5 with ⟨h4, h5⟩
  rcases h4 with ⟨h3, hRoot, hCubic, hTrans, h4⟩
  rcases h3 with ⟨h2, h3⟩
  rcases h2 with ⟨h1, h2⟩
  have h1' := coupled_N01Properties_restrict hT h1 hb hε hε'
  have h2' := coupled_N02Properties_restrict h2 hb hε
  have h3' := coupled_N03Properties_restrict h3 hb hε
  have h4' := coupled_N04Properties_restrict h4 hb hε
  have h6' := coupled_N06Properties_restrict h6 hb hε hε'
  have hG' := coupled_scalarInverseProperties_restrict hG hb hε
  have hBridge' := coupled_scalarBanachBridgeProperties_restrict hBridge hb hε
  have h8' := coupled_N08Properties_restrict h8 hb hε
  exact ⟨⟨⟨⟨⟨⟨⟨h1', h2'⟩, h3'⟩, hRoot, hCubic, hTrans, h4'⟩, h5⟩, h6'⟩,
    hG', hBridge'⟩, h8'⟩

end ContinuousFlexibility.Statements
