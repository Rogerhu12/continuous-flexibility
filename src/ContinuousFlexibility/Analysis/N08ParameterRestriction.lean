import ContinuousFlexibility.Analysis.N08Neighborhoods
import ContinuousFlexibility.Analysis.StateKappaBounds

/-!
# Retaining the nonlinear construction on a common smaller neighborhood

Every datum through N07 is kept fixed. Larger defining orders and losses,
together with a smaller positive radius, preserve all assertions. The final
joint residual may therefore choose its own common low-order neighborhood
without replacing the already constructed physical scalar inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n08_sample_weights_nonneg {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) :
    ∀ m, 0 ≤ T.H (T.sample m) ∧ 0 ≤ T.E0 (T.sample m) := by
  obtain ⟨C, hC⟩ := hD
  intro m
  have hp := hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hC.2.1 m)
  exact ⟨hp.2.1.le, hp.2.2.1.le⟩

section AbstractBounds

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

private theorem n08_restrict_weighted_jet
    {p : ℕ → Seminorm ℝ E} {U V : Set E} {f : E → ℝ}
    {base base' high high' k : ℕ} {x0 : E} {W : ℝ} (normFun : ℝ → ℝ)
    (hp : Monotone p) (hb : base ≤ base') (hh : high ≤ high')
    (hV : IsOpen V) (hVU : V ⊆ U) (hW : 0 ≤ W)
    (h : ∃ J : SmoothDirections U f, ∀ x ∈ U, ∀ v : Fin k → E,
      normFun (J.D k x v) ≤ W * oneHighVariationWeight p base high (x - x0) v) :
    ∃ J : SmoothDirections V f, ∀ x ∈ V, ∀ v : Fin k → E,
      normFun (J.D k x v) ≤ W * oneHighVariationWeight p base' high' (x - x0) v := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨smoothDirectionsRestrict J hV hVU, fun x hx v => ?_⟩
  exact (hJ x (hVU hx) v).trans (mul_le_mul_of_nonneg_left
    (n08_oneHighVariationWeight_mono hp hb hh (x - x0) v) hW)

private theorem n08_linear_state_weight_mono
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {loss loss' : ℕ} (hl : loss ≤ loss') (s : ℕ) (x0 : E) (z : E × ℝ)
    {a A : ℝ} (hA : 0 ≤ A)
    (h : a ≤ A * (1 + p (s + loss) (z.1 - x0) + |z.2|)) :
    a ≤ A * (1 + p (s + loss') (z.1 - x0) + |z.2|) :=
  h.trans (mul_le_mul_of_nonneg_left (add_le_add_right
    (add_le_add_left (hp (Nat.add_le_add_left hl s) (z.1 - x0)) 1) _) hA)

end AbstractBounds

/- These aliases isolate the two large final conjuncts of N01 so each
restriction proof elaborates and checks independently of the geometric data. -/
private def n08CoefficientTowerBounds (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b p,
    a + b ≤ s → p.1 ∈ D.cells m →
    ∃ J : SmoothDirections (stateNeighborhood S C base ε) (coefficientFamily D S C i a b p),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0)) v

private def n08FlowTowerBounds (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a b p,
    a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
    ∃ J : SmoothDirections (stateNeighborhood S C base ε) (ordinaryFlowFamily S C m a b p),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0)) v

private theorem n08_coefficientTowerBounds_mono
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hweights : ∀ m, 0 ≤ T.H (T.sample m) ∧ 0 ≤ T.E0 (T.sample m))
    (h : n08CoefficientTowerBounds D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    n08CoefficientTowerBounds D T S C base' loss' ε' := by
  have hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hb hε
  have hopen : IsOpen (stateNeighborhood S C base' ε') :=
    n08_isOpen_stateNeighborhood S C base' ε'
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    pairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  intro k s
  obtain ⟨B, hB, hBj⟩ := h k s
  refine ⟨B, hB, fun m i a b p hab hpm => ?_⟩
  have hc : 0 ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (hweights m).1 _))
      (Real.rpow_nonneg (hweights m).2 _)
  exact n08_restrict_weighted_jet abs hp hb (Nat.add_le_add_left hl s)
    hopen hsub hc (hBj m i a b p hab hpm)

private theorem n08_flowTowerBounds_mono
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hweights : ∀ m, 0 ≤ T.H (T.sample m) ∧ 0 ≤ T.E0 (T.sample m))
    (h : n08FlowTowerBounds D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    n08FlowTowerBounds D T S C base' loss' ε' := by
  have hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hb hε
  have hopen : IsOpen (stateNeighborhood S C base' ε') :=
    n08_isOpen_stateNeighborhood S C base' ε'
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    pairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  intro k s
  obtain ⟨B, hB, hBj⟩ := h k s
  refine ⟨B, hB, fun m a b p hab hpm => ?_⟩
  have hc : 0 ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (hweights (C.cell m)).1 _))
      (Real.rpow_nonneg (hweights (C.cell m)).2 _)
  exact n08_restrict_weighted_jet
    (fun t => min (p.1 - C.left m) (C.right m - p.1) ^ a * |t|)
    hp hb (Nat.add_le_add_left hl s) hopen hsub hc (hBj m a b p hab hpm)

/-- Preserve the actual coefficients and flow towers on a smaller neighborhood. -/
theorem n08_n01Properties_mono
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    N01Properties D T S C base' loss' ε' := by
  obtain ⟨hRef, _, hreference, hcontrol, hindex, hjets, hflow, hchart, hreturns,
    hgeometry, hcritical, hcoeff, hflowJets⟩ := h
  have hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hb hε
  have hweights : ∀ m, 0 ≤ T.H (T.sample m) ∧ 0 ≤ T.E0 (T.sample m) :=
    n08_sample_weights_nonneg hT hRef.1
  have hcoeff' : n08CoefficientTowerBounds D T S C base' loss' ε' :=
    n08_coefficientTowerBounds_mono hweights hcoeff hb hl hε
  have hflowJets' : n08FlowTowerBounds D T S C base' loss' ε' :=
    n08_flowTowerBounds_mono hweights hflowJets hb hl hε
  exact ⟨hRef, hεpos, hreference, hcontrol, hindex, hjets,
    (fun z hz => hflow z (hsub hz)), (fun z hz => hchart z (hsub hz)),
    (fun z hz => hreturns z (hsub hz)), (fun z hz => hgeometry z (hsub hz)),
    (fun z hz => hcritical z (hsub hz)), hcoeff', hflowJets'⟩

/-- Restriction leaves the actual return residual and chart derivative unchanged. -/
theorem n08_n02Properties_mono
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N02Properties D T S C R base ε) (hb : base ≤ base') (hε : ε' ≤ ε) :
    N02Properties D T S C R base' ε' := by
  obtain ⟨hcharts, hresidual, hzero, hlinear, herror, hincrement, hderivative,
    hright, hleft, hinverse, hsmooth⟩ := h
  have hsub := n08_stateNeighborhood_mono (C := C) hb hε
  have hsector := n08_sectorNeighborhood_mono (S := S) hb hε hε
  exact ⟨(fun z hz => hcharts z (hsub hz)), (fun z hz => hresidual z (hsub hz)),
    (fun z hz => hzero z (hsub hz)), hlinear, (fun z hz => herror z (hsub hz)),
    (fun z hz => hincrement z (hsub hz)), (fun z hz => hderivative z (hsub hz)),
    hright, hleft, hinverse,
    smoothTameOn_mono hsmooth (n08_isOpen_sectorNeighborhood S base' ε' ε') hsector⟩

/-- The same correction has all its original identities on the smaller domain. -/
theorem n08_n03Properties_mono
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N03Properties D T S C R L base ε) (hb : base ≤ base') (hε : ε' ≤ ε) :
    N03Properties D T S C R L base' ε' := by
  obtain ⟨ha, hpositive, hturning, hparity, hflow, hdifference, hconservation, hsmooth⟩ := h
  have hsub := n08_stateNeighborhood_mono (C := C) hb hε
  have hsector := n08_sectorNeighborhood_mono (S := S) hb hε hε
  refine ⟨(fun z hz => ha z (hsub hz)), (fun z hz => hpositive z (hsub hz)),
    (fun z hz => hturning z (hsub hz)), (fun z hz => hparity z (hsub hz)),
    (fun z hz => hflow z (hsub hz)), (fun z hz => hdifference z (hsub hz)),
    (fun z hz => hconservation z (hsub hz)), ?_⟩
  exact smoothTameOn_mono hsmooth
    (((n08_isOpen_sectorNeighborhood S base' ε' ε').prod isOpen_univ).prod isOpen_univ)
    (Set.prod_mono (Set.prod_mono hsector (subset_refl _)) (subset_refl _))

private def n08CanonicalCoefficientBounds (S : PhysicalSpacesData) (T : MaterialData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
    p ∈ canonicalOpen S K m → ∀ a b : ℕ, a + b ≤ s →
      |mixedDerivative a b (K.potential z m) p| +
      |mixedDerivative a b (K.dividedDifference z m).a p| +
      |mixedDerivative a b (K.dividedDifference z m).b p| +
      |mixedDerivative a b (K.dividedDifference z m).c p| ≤
        A * T.E0 (T.sample (K.cell m)) ^ A *
          (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)

private theorem n08_canonicalCoefficientBounds_mono
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hE : ∀ m, 0 ≤ T.E0 (T.sample m))
    (h : n08CanonicalCoefficientBounds S T C K base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    n08CanonicalCoefficientBounds S T C K base' loss' ε' := by
  have hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hb hε
  intro s
  obtain ⟨A, hA, hAs⟩ := h s
  refine ⟨A, hA, ?_⟩
  intro z hz m p hp a b hab
  exact n08_linear_state_weight_mono (solve_stateGrading_monotone S) hl s C.referenceState z
    (mul_nonneg hA.le (Real.rpow_nonneg (hE (K.cell m)) _)) (hAs z (hsub hz) m p hp a b hab)

/-- Only the displayed state grading changes in the coordinate estimates;
all charts, source transforms, cuts and transmission identities are retained. -/
theorem n08_n04Properties_mono
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hE : ∀ m, 0 ≤ T.E0 (T.sample m))
    (h : N04Properties D T S C L K base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    N04Properties D T S C L K base' loss' ε' := by
  obtain ⟨hopen, hsupport, hfixed, hinterval, hpositive, hnegative, hcover,
    hcharts, hboundary, hparity, hinverse, hcuts, htransmission, hoperator,
    hnormal, hcubic, hbound, hintegral⟩ := h
  have hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hb hε
  have hbound' : n08CanonicalCoefficientBounds S T C K base' loss' ε' :=
    n08_canonicalCoefficientBounds_mono hE hbound hb hl hε
  exact ⟨hopen, hsupport, (fun z hz => hfixed z (hsub hz)),
    hinterval, hpositive, hnegative, hcover,
    (fun z hz => hcharts z (hsub hz)), (fun z hz => hboundary z (hsub hz)),
    (fun z hz => hparity z (hsub hz)), (fun z hz => hinverse z (hsub hz)), hcuts,
    (fun z hz => htransmission z (hsub hz)), (fun z hz => hoperator z (hsub hz)),
    (fun z hz => hnormal z (hsub hz)), (fun z hz => hcubic z (hsub hz)), hbound',
    (fun z hz => hintegral z (hsub hz))⟩

/-- The Banach inverse is unchanged; only its state neighborhood is restricted. -/
theorem n08_n06Properties_mono
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {L : ReturnCorrectionData S} {V : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N06Properties D S C K L V b B P base ε)
    (hb : base ≤ base') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    N06Properties D S C K L V b B P base' ε' := by
  have hsub := n08_stateNeighborhood_mono (C := C) hb hε
  exact ⟨hεpos, fun z hz => h.2 z (hsub hz)⟩

/-- Restrict the genuine inverse family and both of its tame assertions. -/
theorem n08_scalarInverseProperties_mono
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {G : ScalarInverseData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : ScalarInverseProperties D S C L G base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    ScalarInverseProperties D S C L G base' ε' := by
  obtain ⟨hsolve, hunique, htame, hsmooth⟩ := h
  have hsub := n08_stateNeighborhood_mono (C := C) hb hε
  have hsector := n08_sectorNeighborhood_mono (S := S) hb hε hε
  exact ⟨(fun z hz => hsolve z (hsub hz)), (fun z hz => hunique z (hsub hz)),
    n08_linearFamilyTame_restrict htame hsector,
    smoothTameOn_mono hsmooth
      ((n08_isOpen_sectorNeighborhood S base' ε' ε').prod isOpen_univ)
      (Set.prod_mono hsector (subset_refl _))⟩

/-- The bridge still identifies the physical solution with the same Banach
inverse and the same canonical representative. -/
theorem n08_scalarBanachBridgeProperties_mono
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {V : VolumeModelData S K} {b : ℕ}
    {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
    {G : ScalarInverseData S} {base base' : ℕ} {ε ε' : ℝ}
    (h : ScalarBanachBridgeProperties D S C K V b B P G base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    ScalarBanachBridgeProperties D S C K V b B P G base' ε' := by
  obtain ⟨s, hs, A, hA, hAs⟩ := h
  have hsub := n08_stateNeighborhood_mono (C := C) hb hε
  exact ⟨s, hs, A, hA, fun z hz => hAs z (hsub hz)⟩

section Cumulative

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {V : VolumeModelData S K} {b : ℕ}
  {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
  {G : ScalarInverseData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}

theorem n08_through01_mono (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough01 D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough01 D T S C base' loss' ε' :=
  n08_n01Properties_mono hT h hb hl hεpos hε

theorem n08_through02_mono (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough02 D T S C R base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough02 D T S C R base' loss' ε' :=
  ⟨n08_through01_mono hT h.1 hb hl hεpos hε, n08_n02Properties_mono h.2 hb hε⟩

theorem n08_through03_mono (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough03 D T S C R L base' loss' ε' :=
  ⟨n08_through02_mono hT h.1 hb hl hεpos hε, n08_n03Properties_mono h.2 hb hε⟩

theorem n08_through04_mono (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough04 D T S C R L K base' loss' ε' := by
  obtain ⟨hprev, hroot, hcubic, htransmission, hcoordinates⟩ := h
  have hN01 : N01Properties D T S C base loss ε := hprev.1.1
  have hweights := n08_sample_weights_nonneg hT hN01.1.1
  exact ⟨n08_through03_mono hT hprev hb hl hεpos hε, hroot, hcubic, htransmission,
    n08_n04Properties_mono (fun m => (hweights m).2) hcoordinates hb hl hε⟩

theorem n08_through05_mono (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough05 D T S C R L K V b B base' loss' ε' :=
  ⟨n08_through04_mono hT h.1 hb hl hεpos hε, h.2⟩

theorem n08_through06_mono (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough06 D T S C R L K V b B P base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough06 D T S C R L K V b B P base' loss' ε' :=
  ⟨n08_through05_mono hT h.1 hb hl hεpos hε,
    n08_n06Properties_mono h.2 hb hεpos hε⟩

/-- All prior stages, their same witnesses and their inverse identities survive
one common enlargement of the orders and reduction of the radius. -/
theorem n08_through07_mono (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough07 D T S C R L K V b B P G base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough07 D T S C R L K V b B P G base' loss' ε' :=
  ⟨n08_through06_mono hT h.1 hb hl hεpos hε,
    n08_scalarInverseProperties_mono h.2.1 hb hε,
    n08_scalarBanachBridgeProperties_mono h.2.2 hb hε⟩

/-- Radius restriction as a convenient special case of the common-parameter lemma. -/
theorem n08_through07_shrink (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough07 D T S C R L K V b B P G base loss ε)
    (hεpos : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough07 D T S C R L K V b B P G base loss ε' :=
  n08_through07_mono hT h le_rfl le_rfl hεpos hε

end Cumulative

end ContinuousFlexibility.Statements
