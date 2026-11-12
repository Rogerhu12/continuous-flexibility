import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.StateKappaBounds
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.TameTransfer
import ContinuousFlexibility.Analysis.N07aNeighborhood

/-!
# Restricting the common nonlinear neighborhood

The relative perturbation is estimated on a smaller neighborhood and may
require a higher low order.  Every property already constructed through N05
is retained on that same neighborhood.  No change of the canonical charts,
the source spaces, or the reference graph is involved.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n06_stateNeighborhood_mono {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' : ℕ} {ε ε' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨(solve_stateGrading_monotone S hb (z.1 - C.referenceState)).trans_lt
    (hz.1.trans_le hε), hz.2.trans_le hε⟩

theorem n06_sectorNeighborhood_mono {S : PhysicalSpacesData}
    {base base' : ℕ} {ε ε' q q' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) (hq : q' ≤ q) :
    sectorNeighborhood S base' ε' q' ⊆ sectorNeighborhood S base ε q := by
  intro z hz
  exact ⟨(solve_sectorGrading_monotone S hb z.1).trans_lt
    (hz.1.trans_le hε), hz.2.trans_le hq⟩

theorem n06_isOpen_stateNeighborhood (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    IsOpen (stateNeighborhood S C base ε) := by
  exact (isOpen_lt (((solve_stateGrading_withSeminorms S).continuous_seminorm base).comp
    (continuous_fst.sub continuous_const)) continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)

theorem n06_isOpen_sectorNeighborhood (S : PhysicalSpacesData)
    (base : ℕ) (ε q : ℝ) : IsOpen (sectorNeighborhood S base ε q) := by
  exact (isOpen_lt (((solve_sectorGrading_withSeminorms S).continuous_seminorm base).comp
    continuous_fst) continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)

theorem n06_oneHighVariationWeight_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {base base' high high' : ℕ}
    (hb : base ≤ base') (hh : high ≤ high') {k : ℕ} (x : E) (v : Fin k → E) :
    oneHighVariationWeight p base high x v ≤
      oneHighVariationWeight p base' high' x v := by
  simpa only [tameJetSize, oneHighVariationWeight, Nat.zero_add] using
    (tameJetSize_mono hp hh hb k 0 x v)

private theorem n06_forall_mem_mono {α : Type*} {U V : Set α}
    (hVU : V ⊆ U) {P : α → Prop} (h : ∀ x ∈ U, P x) : ∀ x ∈ V, P x :=
  fun x hx => h x (hVU hx)

private theorem n06_uniform_bound_mono {α ι : Type*} {U V : Set α}
    (hVU : V ⊆ U) {P : ι → ℝ → α → Prop}
    (h : ∀ i, ∃ B : ℝ, 0 < B ∧ ∀ x ∈ U, P i B x) :
    ∀ i, ∃ B : ℝ, 0 < B ∧ ∀ x ∈ V, P i B x := by
  intro i
  obtain ⟨B, hB, hbound⟩ := h i
  exact ⟨B, hB, n06_forall_mem_mono hVU hbound⟩

private theorem n06_directional_bound_mono
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U V : Set E} {f : E → ℝ} {p : ℕ → Seminorm ℝ E}
    {k base base' high : ℕ} {K w : ℝ} {x₀ : E}
    (hp : Monotone p) (hb : base ≤ base') (hK : 0 ≤ K)
    (hV : IsOpen V) (hVU : V ⊆ U)
    (h : ∃ J : SmoothDirections U f, ∀ x ∈ U, ∀ v : Fin k → E,
      w * |J.D k x v| ≤ K * oneHighVariationWeight p base high (x - x₀) v) :
    ∃ J : SmoothDirections V f, ∀ x ∈ V, ∀ v : Fin k → E,
      w * |J.D k x v| ≤ K * oneHighVariationWeight p base' high (x - x₀) v := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨smoothDirectionsRestrict J hV hVU, ?_⟩
  intro x hx v
  change w * |J.D k x v| ≤ _
  exact (hJ x (hVU hx) v).trans (mul_le_mul_of_nonneg_left
    (n06_oneHighVariationWeight_mono hp hb le_rfl (x - x₀) v) hK)

private theorem n06_coefficientJet_bounds_mono
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U V : Set E} {p : ℕ → Seminorm ℝ E} {x₀ : E}
    {H E₀ : ℕ → ℝ} {cells : ℕ → Set ℝ}
    {family : Fin 3 → ℕ → ℕ → PolarPoint → E → ℝ}
    {base base' loss : ℕ}
    (hH : ∀ m, 0 < H m) (hE : ∀ m, 0 < E₀ m)
    (hp : Monotone p) (hV : IsOpen V) (hVU : V ⊆ U) (hb : base ≤ base')
    (h : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b y,
      a + b ≤ s → y.1 ∈ cells m →
      ∃ J : SmoothDirections U (family i a b y),
        ∀ z ∈ U, ∀ v : Fin k → E,
          |J.D k z v| ≤ B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B *
            oneHighVariationWeight p base (s + loss) (z - x₀) v) :
    ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b y,
      a + b ≤ s → y.1 ∈ cells m →
      ∃ J : SmoothDirections V (family i a b y),
        ∀ z ∈ V, ∀ v : Fin k → E,
          |J.D k z v| ≤ B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B *
            oneHighVariationWeight p base' (s + loss) (z - x₀) v := by
  intro k s
  obtain ⟨B, hB, hJ⟩ := h k s
  refine ⟨B, hB, ?_⟩
  intro m i a b y hab hy
  have hK : 0 ≤ B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_pos_of_pos (hH m) _).le)
      (Real.rpow_pos_of_pos (hE m) _).le
  have hj := hJ m i a b y hab hy
  have hresult := n06_directional_bound_mono
    (E := E) (U := U) (V := V) (f := family i a b y) (p := p)
    (k := k) (base := base) (base' := base') (high := s + loss)
    (K := B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B) (w := 1) (x₀ := x₀)
    hp hb hK hV hVU (by simpa only [one_mul] using hj)
  simpa only [one_mul] using hresult

private theorem n06_flowJet_bounds_mono
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U V : Set E} {p : ℕ → Seminorm ℝ E} {x₀ : E}
    {H E₀ left right : ℕ → ℝ}
    {family : ℕ → ℕ → ℕ → PolarPoint → E → ℝ}
    {base base' loss : ℕ}
    (hH : ∀ m, 0 < H m) (hE : ∀ m, 0 < E₀ m)
    (hp : Monotone p) (hV : IsOpen V) (hVU : V ⊆ U) (hb : base ≤ base')
    (h : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a b y,
      a + b ≤ s → y.1 ∈ Ioo (left m) (right m) →
      ∃ J : SmoothDirections U (family m a b y),
        ∀ z ∈ U, ∀ v : Fin k → E,
          min (y.1 - left m) (right m - y.1) ^ a * |J.D k z v| ≤
            B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B *
            oneHighVariationWeight p base (s + loss) (z - x₀) v) :
    ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a b y,
      a + b ≤ s → y.1 ∈ Ioo (left m) (right m) →
      ∃ J : SmoothDirections V (family m a b y),
        ∀ z ∈ V, ∀ v : Fin k → E,
          min (y.1 - left m) (right m - y.1) ^ a * |J.D k z v| ≤
            B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B *
            oneHighVariationWeight p base' (s + loss) (z - x₀) v := by
  intro k s
  obtain ⟨B, hB, hJ⟩ := h k s
  refine ⟨B, hB, ?_⟩
  intro m a b y hab hy
  have hK : 0 ≤ B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_pos_of_pos (hH m) _).le)
      (Real.rpow_pos_of_pos (hE m) _).le
  exact n06_directional_bound_mono
    (E := E) (U := U) (V := V) (f := family m a b y) (p := p)
    (k := k) (base := base) (base' := base') (high := s + loss)
    (K := B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B)
    (w := min (y.1 - left m) (right m - y.1) ^ a) (x₀ := x₀)
    hp hb hK hV hVU (hJ m a b y hab hy)

theorem n06_N01Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    N01Properties D T S C base' loss ε' := by
  rcases h with ⟨hRef, _, hstate, hcontrol, hshift, hcontrolBounds, hflow,
    hleft, hreturn, hgeometry, hfixed, hcoefficient, hflowJet⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  obtain ⟨_, hprofile⟩ := hRef.1
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hprofile.2.1 m
  have hH (m : ℕ) : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  have hE (m : ℕ) : 0 < T.E0 (T.sample m) := (hT.2.1 _ (hsample m)).2.2.1
  have hpair : Monotone (pairGrading (stateGrading S) realGrading) :=
    pairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  have hopen := n06_isOpen_stateNeighborhood S C base' ε'
  have hcoefficient' := n06_coefficientJet_bounds_mono
    (E := AnnularState S × ℝ) (U := stateNeighborhood S C base ε)
    (V := stateNeighborhood S C base' ε')
    (p := pairGrading (stateGrading S) realGrading) (x₀ := (C.referenceState, 0))
    (H := fun m => T.H (T.sample m)) (E₀ := fun m => T.E0 (T.sample m))
    (cells := D.cells) (family := coefficientFamily D S C)
    (base := base) (base' := base') (loss := loss)
    hH hE hpair hopen hU hb hcoefficient
  have hflowJet' := n06_flowJet_bounds_mono
    (E := AnnularState S × ℝ) (U := stateNeighborhood S C base ε)
    (V := stateNeighborhood S C base' ε')
    (p := pairGrading (stateGrading S) realGrading) (x₀ := (C.referenceState, 0))
    (H := fun m => T.H (T.sample (C.cell m)))
    (E₀ := fun m => T.E0 (T.sample (C.cell m)))
    (left := C.left) (right := C.right) (family := ordinaryFlowFamily S C)
    (base := base) (base' := base') (loss := loss)
    (fun m => hH (C.cell m)) (fun m => hE (C.cell m)) hpair hopen hU hb hflowJet
  exact ⟨hRef, hε', hstate, hcontrol, hshift, hcontrolBounds,
    n06_forall_mem_mono hU hflow, n06_forall_mem_mono hU hleft,
    n06_forall_mem_mono hU hreturn, n06_forall_mem_mono hU hgeometry,
    n06_forall_mem_mono hU hfixed, hcoefficient', hflowJet'⟩

theorem n06_N02Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {base base' : ℕ} {ε ε' : ℝ}
    (h : N02Properties D T S C R base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N02Properties D T S C R base' ε' := by
  rcases h with ⟨hflow, hresidual, hzero, hlinear, herror, hincrement,
    hderivative, hright, hleft, hinverseTame, hresidualTame⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  refine ⟨(fun z hz => hflow z (hU hz)), (fun z hz => hresidual z (hU hz)),
    (fun z hz => hzero z (hU hz)), hlinear, (fun z hz => herror z (hU hz)),
    (fun z hz => hincrement z (hU hz)), (fun z hz => hderivative z (hU hz)),
    hright, hleft, hinverseTame, ?_⟩
  exact smoothTameOn_mono hresidualTame (n06_isOpen_sectorNeighborhood S base' ε' ε')
    (n06_sectorNeighborhood_mono hb hε hε)

theorem n06_N03Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N03Properties D T S C R L base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N03Properties D T S C R L base' ε' := by
  rcases h with ⟨ha, hpositive, hzero, hparity, hflow, hoperator, hintegral,
    htame, hspatial⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  refine ⟨(fun z hz => ha z (hU hz)), (fun z hz => hpositive z (hU hz)),
    (fun z hz => hzero z (hU hz)), (fun z hz => hparity z (hU hz)),
    (fun z hz => hflow z (hU hz)), (fun z hz => hoperator z (hU hz)),
    (fun z hz => hintegral z (hU hz)), ?_, fun z hz => hspatial z (hU hz)⟩
  exact smoothTameOn_mono htame
    (((n06_isOpen_sectorNeighborhood S base' ε' ε').prod isOpen_univ).prod isOpen_univ)
    (Set.prod_mono (Set.prod_mono (n06_sectorNeighborhood_mono hb hε hε)
      (subset_refl _)) (subset_refl _))

/-- Actual current domains and their boundary germs restrict with the
same geometry when the nonlinear neighborhood shrinks. -/
theorem n06_CanonicalGeometry_mono {D : ReferenceData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : CanonicalGeometry D S C K base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    CanonicalGeometry D S C K base' ε' := by
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  exact {
    normalizationOpen := h.normalizationOpen
    normalizationSupport := h.normalizationSupport
    normalization := fun z hz => h.normalization z (hU hz)
    referenceBounds := h.referenceBounds
    referencePositive := h.referencePositive
    referenceNegative := h.referenceNegative
    referencePartition := h.referencePartition
    referenceDomain := h.referenceDomain
    domains := fun z hz => h.domains z (hU hz)
    partition := fun z hz => h.partition z (hU hz)
    charts := fun z hz => h.charts z (hU hz)
    boundary := fun z hz => h.boundary z (hU hz)
    reflection := fun z hz => h.reflection z (hU hz)
    inverseReflection := fun z hz => h.inverseReflection z (hU hz) }

theorem n06_N04Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (h : N04Properties D T S C L K base loss ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    N04Properties D T S C L K base' loss ε' := by
  rcases h with ⟨hgeometry, hoperator, hbounds, hpairing⟩
  rcases hoperator with ⟨hcuts, htransmission, hoperator, hnegative, hpositive⟩
  have hU := n06_stateNeighborhood_mono (C := C) hb hε
  exact ⟨n06_CanonicalGeometry_mono hgeometry hb hε,
    ⟨⟨hcuts.1, n06_forall_mem_mono hU hcuts.2⟩,
      n06_forall_mem_mono hU htransmission, n06_forall_mem_mono hU hoperator,
      n06_forall_mem_mono hU hnegative, n06_forall_mem_mono hU hpositive⟩,
    n06_uniform_bound_mono hU hbounds, n06_forall_mem_mono hU hpairing⟩

private theorem n06_parameter_bound_mono {α : Type*} {U V : Set α}
    (hVU : V ⊆ U) {P : ℕ → ℕ → ℝ → ℝ → α → Prop}
    (h : ∃ r d : ℕ, ∃ C₀ A : ℝ, 0 < C₀ ∧ 0 ≤ A ∧
      ∀ z ∈ U, P r d C₀ A z) :
    ∃ r d : ℕ, ∃ C₀ A : ℝ, 0 < C₀ ∧ 0 ≤ A ∧
      ∀ z ∈ V, P r d C₀ A z := by
  obtain ⟨r, d, C₀, A, hC₀, hA, hbound⟩ := h
  exact ⟨r, d, C₀, A, hC₀, hA, n06_forall_mem_mono hVU hbound⟩

set_option backward.isDefEq.respectTransparency true in
/-- Restriction retains the primitive bounds with their original constants
and the same geometric fields. -/
theorem n06_CanonicalPrimitiveGeometry_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    CanonicalPrimitiveGeometry D T S C L K base' ε' := by
  have hU : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε :=
    n06_stateNeighborhood_mono (S := S) (C := C) hb hε
  exact {
    materialJets := fun N => n06_parameter_bound_mono
      (α := AnnularState S × ℝ) hU (h.materialJets N)
    transport := n06_forall_mem_mono
      (α := AnnularState S × ℝ) hU h.transport
    physicalCoefficients := n06_forall_mem_mono
      (α := AnnularState S × ℝ) hU h.physicalCoefficients }

/-- Every geometric jet and transition certificate is retained on the
same smaller neighborhood as the original nonlinear construction. -/
theorem n06_NonlinearPropertiesThrough05_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough05 D T S C R L K V b B base' loss ε' := by
  rcases h with ⟨⟨⟨⟨h01, h02⟩, h03⟩, hroot, hcubic, htransmission, h04, hprimitive⟩, h05⟩
  exact ⟨⟨⟨⟨n06_N01Properties_mono hT h01 hb hε' hε,
    n06_N02Properties_mono h02 hb hε⟩, n06_N03Properties_mono h03 hb hε⟩,
    hroot, hcubic, htransmission, n06_N04Properties_mono h04 hb hε,
      n07a_primitiveGeometry_restrict h01.1.1 hT hprimitive.1 hb hε,
      n06_CanonicalPrimitiveGeometry_mono hprimitive.2 hb hε⟩, h05⟩

end ContinuousFlexibility.Statements
