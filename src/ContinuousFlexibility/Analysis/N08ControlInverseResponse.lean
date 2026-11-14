module

public import ContinuousFlexibility.Analysis.N08SectorControlColumn
public import ContinuousFlexibility.Analysis.N08ControlResponseBounds

/-!
# All-order control responses through the existing scalar inverse

The same actual smoothing column is used on sector states and extended by
zero elsewhere. Its low source norm is uniformly bounded on a single
stronger neighborhood, so the existing inverse-family estimate has only
one high state factor. The bound includes the source, the full height pair,
and the scalar compatibility response at every output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem n08_linear_response_zero
    {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (p : Seminorm ℝ X) (q : Seminorm ℝ Y) (L : X →ₗ[ℝ] (Y × ℝ))
    {f : X} (hf : f = 0) :
    p f + q (L f).1 + |(L f).2| = 0 := by
  simp only [hf, map_zero, Prod.fst_zero, Prod.snd_zero, abs_zero, add_zero]

private theorem n08_with_positive_column_witness
    {W : Type*} {Condition : ℕ → ℕ → ℝ → W → Prop} {P : Prop}
    (h : ∃ b l : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ w : W, Condition b l δ w)
    (hP : ∀ b l : ℕ, ∀ δ : ℝ, 0 < δ → ∀ w : W, Condition b l δ w → P) : P := by
  obtain ⟨b, l, δ, hδ, w, hw⟩ := h
  exact hP b l δ hδ w hw

private theorem n08_with_response_orders
    {Condition : ℕ → ℕ → Prop} {P : Prop}
    (h : ∃ b l : ℕ, Condition b l) (hP : ∀ b l : ℕ, Condition b l → P) : P := by
  obtain ⟨b, l, hbl⟩ := h
  exact hP b l hbl

private theorem n08_with_nonnegative_response_bound
    {Condition : ℝ → Prop} {P : Prop}
    (h : ∃ K : ℝ, 0 ≤ K ∧ Condition K)
    (hP : ∀ K : ℝ, 0 ≤ K → Condition K → P) : P := by
  obtain ⟨K, hK, hCondition⟩ := h
  exact hP K hK hCondition

private theorem n08_with_positive_response_bound
    {Condition : ℝ → Prop} {P : Prop}
    (h : ∃ K : ℝ, 0 < K ∧ Condition K)
    (hP : ∀ K : ℝ, 0 < K → Condition K → P) : P := by
  obtain ⟨K, hK, hCondition⟩ := h
  exact hP K hK hCondition

private theorem n08_transport_predicate
    {X : Type*} (P : X → Prop) {x y : X}
    (hxy : x = y) (hx : P x) : P y :=
  hxy ▸ hx

private theorem n08_transport_response_bound
    {X : Type*} (response : X → ℝ) {x y : X} {g h : ℝ}
    (hxy : x = y) (hgh : g = h) (K n : ℝ)
    (hb : response x ≤ K * (1 + g) * n) :
    response y ≤ K * (1 + h) * n :=
  (congrArg response hxy).symm.trans_le
    (hb.trans_eq (congrArg (fun a : ℝ => K * (1 + a) * n) hgh))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {base loss : ℕ} {ε : ℝ}

/-- Transport the raw column estimate before introducing the inverse witness.
Keeping this step separate prevents elaboration from unfolding the full
physical construction while checking an elementary equality of seminorms. -/
private theorem n08_sectorColumn_source_bound
    (href : referenceStateConditions D S C)
    (Hraw : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    {V : Set (StateDirections S × ℝ)} {columnBase columnLoss : ℕ} {δ : ℝ}
    (hmap : MapsTo (liftSectorParameter S C) V
      {z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ})
    (hcolumn : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z,
      n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ →
      ∀ b : ControlBanach, S.sourceGrading s (Hraw z b) ≤
        K * (1 + n08StateParameterGrading S (s + columnLoss)
          (z - (C.referenceState, 0))) * ‖b‖) :
    ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ V, ∀ b : ControlBanach,
      S.sourceGrading s (n08SectorControlColumn S Hraw (liftSectorParameter S C z) b) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + columnLoss) z) * ‖b‖ := by
  intro s
  refine n08_with_nonnegative_response_bound (hcolumn s) ?_
  intro K hK hKb
  refine ⟨K, hK, ?_⟩
  intro z hz b
  have hb := hKb (liftSectorParameter S C z) (hmap hz) b
  have heval : Hraw (liftSectorParameter S C z) b =
      n08SectorControlColumn S Hraw (liftSectorParameter S C z) b :=
    (congrArg (fun F : ControlBanach →L[ℝ] S.Source => F b)
      (n08SectorControlColumn_lift href Hraw z)).symm
  exact n08_transport_response_bound (X := S.Source) (S.sourceGrading s) heval
    (n08_liftSectorParameter_difference S C (s + columnLoss) z) K ‖b‖ hb

/-- Restrict the derivative using an abstract residual and transport only
its value, without rewriting inside the physical residual construction. -/
private theorem n08_sectorColumn_lineDeriv
    (F : AnnularState S × ℝ → S.Source)
    (Hraw : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    {columnBase newBase : ℕ} {δ η : ℝ}
    (hbase : columnBase ≤ newBase) (hradius : 2 * η ≤ δ)
    (hderiv : ∀ z : AnnularState S × ℝ,
      n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ →
      ∀ u : CircleSpace S,
        HasProjectiveLineDerivAt (fun x : AnnularState S => F (x, z.2))
          (Hraw z (n08ControlRestriction S u)) z.1 (0, (0, (u, 0)))) :
    ∀ z ∈ stateNeighborhood S C newBase η, stateSector S z.1 →
      ∀ u : CircleSpace S,
        HasProjectiveLineDerivAt (fun x : AnnularState S => F (x, z.2))
          (n08SectorControlColumn S Hraw z (n08ControlRestriction S u))
          z.1 (0, (0, (u, 0))) := by
  intro z hz hs u
  have hball : n08StateParameterGrading S columnBase
      (z - (C.referenceState, 0)) < δ :=
    (n08_stateNeighborhood_pairGrading_lt
      (S := S) (C := C) (base := newBase) (s := columnBase)
      (ε := η) (z := z) hbase hz).trans_le hradius
  have heval : Hraw z (n08ControlRestriction S u) =
      n08SectorControlColumn S Hraw z (n08ControlRestriction S u) :=
    (congrArg (fun A : ControlBanach →L[ℝ] S.Source =>
      A (n08ControlRestriction S u))
      (n08SectorControlColumn_of_sector (S := S) Hraw (z := z) hs)).symm
  exact n08_transport_predicate
    (fun df : S.Source => HasProjectiveLineDerivAt
      (fun x : AnnularState S => F (x, z.2)) df z.1 (0, (0, (u, 0))))
    heval (hderiv z hball u)

/-- Fix all spaces in the generic inverse estimate before assembling
the physical state neighborhood. -/
private theorem n08_sectorColumn_response_orders
    (Hraw : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    {V : Set (StateDirections S × ℝ)} {columnLoss : ℕ}
    (hGv : LinearFamilyTame (pairGrading (sectorGrading S) realGrading)
      (pairGrading (heightPairGrading S) realGrading) S.sourceGrading V
      (fun z : StateDirections S × ℝ =>
        (G.G (liftSectorParameter S C z)).toLinearMap))
    (hHv : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ V, ∀ b : ControlBanach,
      S.sourceGrading s
          (n08SectorControlColumn S Hraw (liftSectorParameter S C z) b) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading
          (s + columnLoss) z) * ‖b‖) :
    ∃ responseBase responseLoss : ℕ, ∀ s : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ z ∈ V, pairGrading (sectorGrading S) realGrading responseBase z < 1 →
      ∀ b : ControlBanach,
        S.sourceGrading s
            (n08SectorControlColumn S Hraw (liftSectorParameter S C z) b) +
          pairGrading (heightPairGrading S) realGrading s
            (G.G (liftSectorParameter S C z)
              (n08SectorControlColumn S Hraw (liftSectorParameter S C z) b)) ≤
          K * (1 + pairGrading (sectorGrading S) realGrading
            (s + responseLoss) z) * ‖b‖ := by
  have hp : Monotone (pairGrading (sectorGrading S) realGrading) :=
    tamePairGrading_monotone (solve_sectorGrading_monotone S)
      weighted_realGrading_monotone
  have hr : Monotone (pairGrading (heightPairGrading S) realGrading) :=
    tamePairGrading_monotone
      (tamePairGrading_monotone (gradedSeminorm_monotone _ _)
        weighted_realGrading_monotone)
      weighted_realGrading_monotone
  exact n08_controlResponse_bound
    (X := StateDirections S × ℝ) (F := S.Source)
    (Y := HeightPair S × ℝ) (B := ControlBanach)
    (p := pairGrading (sectorGrading S) realGrading) (q := S.sourceGrading)
    (r := pairGrading (heightPairGrading S) realGrading) (U := V)
    (G := fun z : StateDirections S × ℝ =>
      (G.G (liftSectorParameter S C z)).toLinearMap)
    (H := fun (z : StateDirections S × ℝ) (b : ControlBanach) =>
      n08SectorControlColumn S Hraw (liftSectorParameter S C z) b)
    (columnLoss := columnLoss) hp hr hGv hHv

/-- Move one already proved sector response estimate to the ambient state
rectangle. The column is zero away from the sector, as in its definition. -/
private theorem n08_sectorResponse_state_bound
    (href : referenceStateConditions D S C)
    (Hraw : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    {V : Set (StateDirections S × ℝ)} {responseBase responseLoss newBase newLoss s : ℕ}
    {η K : ℝ} (hK : 0 < K) (hbase : responseBase ≤ newBase)
    (hloss : responseLoss ≤ newLoss) (hηone : 2 * η ≤ 1)
    (hnewV : sectorNeighborhood S newBase η η ⊆ V)
    (hb : ∀ y ∈ V, pairGrading (sectorGrading S) realGrading responseBase y < 1 →
      ∀ b : ControlBanach,
        S.sourceGrading s (n08SectorControlColumn S Hraw (liftSectorParameter S C y) b) +
          pairGrading (heightPairGrading S) realGrading s
            (G.G (liftSectorParameter S C y)
              (n08SectorControlColumn S Hraw (liftSectorParameter S C y) b)) ≤
          K * (1 + pairGrading (sectorGrading S) realGrading (s + responseLoss) y) * ‖b‖) :
    ∀ z ∈ stateNeighborhood S C newBase η, ∀ b : ControlBanach,
      S.sourceGrading s (n08SectorControlColumn S Hraw z b) +
        heightPairGrading S s (G.G z (n08SectorControlColumn S Hraw z b)).1 +
        |(G.G z (n08SectorControlColumn S Hraw z b)).2| ≤
        K * (1 + stateGrading S (s + newLoss) (z.1 - C.referenceState) + |z.2|) * ‖b‖ := by
  intro z hz b
  let H := n08SectorControlColumn S Hraw
  by_cases hs : stateSector S z.1
  · let y := n08SectorParameterCenter href z hs
    have hy : y ∈ sectorNeighborhood S newBase η η :=
      n08SectorParameterCenter_mem href hs hz
    have hsmall : pairGrading (sectorGrading S) realGrading responseBase y < 1 :=
      (n08_sectorNeighborhood_pairGrading_lt hbase hy).trans_le hηone
    have hby := hb y (hnewV hy) hsmall b
    have hb' : S.sourceGrading s (H z b) +
        pairGrading (heightPairGrading S) realGrading s (G.G z (H z b)) ≤
        K * (1 + n08StateParameterGrading S (s + responseLoss)
          (z - (C.referenceState, 0))) * ‖b‖ :=
      n08_transport_response_bound (X := AnnularState S × ℝ)
        (fun w : AnnularState S × ℝ => S.sourceGrading s (H w b) +
          pairGrading (heightPairGrading S) realGrading s (G.G w (H w b)))
        (n08SectorParameterCenter_lift href z hs)
        (n08SectorParameterCenter_grading href (s + responseLoss) z hs) K ‖b‖ hby
    have hhigh := n08StateParameterGrading_monotone S
      (Nat.add_le_add_left hloss s) (z - (C.referenceState, 0))
    have hfinal := hb'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hhigh) hK.le) (norm_nonneg b))
    change S.sourceGrading s (H z b) +
        (heightPairGrading S s (G.G z (H z b)).1 + |(G.G z (H z b)).2|) ≤
        K * (1 + (stateGrading S (s + newLoss) (z.1 - C.referenceState) + |z.2 - 0|)) * ‖b‖
      at hfinal
    simpa only [sub_zero, add_assoc] using hfinal
  · have heq : H z = 0 := n08SectorControlColumn_of_not_sector Hraw hs
    have hinput : H z b = 0 :=
      congrArg (fun F : ControlBanach →L[ℝ] S.Source => F b) heq
    have hzero := n08_linear_response_zero (X := S.Source) (Y := HeightPair S)
      (S.sourceGrading s) (heightPairGrading S s) (G.G z).toLinearMap hinput
    exact hzero.le.trans (mul_nonneg (mul_nonneg hK.le
      (add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _))) (norm_nonneg _))

/-- Assemble the neighborhood and inverse estimates with an abstract
residual; its concrete construction is needed only by the final application. -/
private theorem n08ControlInverseResponse_of_column
    (F : AnnularState S × ℝ → S.Source)
    (hε : 0 < ε) (href : referenceStateConditions D S C)
    (hG : LinearFamilyTame (pairGrading (sectorGrading S) realGrading)
      (pairGrading (heightPairGrading S) realGrading) S.sourceGrading
      (sectorNeighborhood S base ε ε)
      (fun z : StateDirections S × ℝ =>
        (G.G (liftSectorParameter S C z)).toLinearMap))
    (columnBase columnLoss : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (Hraw : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    (hderiv : ∀ z : AnnularState S × ℝ,
      n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ →
      ∀ u : CircleSpace S,
        HasProjectiveLineDerivAt (fun x : AnnularState S => F (x, z.2))
          (Hraw z (n08ControlRestriction S u)) z.1 (0, (0, (u, 0))))
    (hsmooth : SmoothTameOn (n08ExtendedControlGrading S) S.sourceGrading
      ({z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ}
        ×ˢ univ)
      (fun z : (AnnularState S × ℝ) × ControlBanach => Hraw z.1 z.2))
    (hcolumn : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z,
      n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ →
      ∀ b : ControlBanach, S.sourceGrading s (Hraw z b) ≤
        K * (1 + n08StateParameterGrading S (s + columnLoss)
          (z - (C.referenceState, 0))) * ‖b‖) :
    ∃ newBase newLoss : ℕ, ∃ η : ℝ,
      base ≤ newBase ∧ loss ≤ newLoss ∧ 0 < η ∧ η ≤ ε ∧
      ∃ H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source,
        (∀ z, ¬ stateSector S z.1 → H z = 0) ∧
        (∀ z ∈ stateNeighborhood S C newBase η, stateSector S z.1 →
          ∀ u : CircleSpace S,
          HasProjectiveLineDerivAt
            (fun x : AnnularState S => F (x, z.2))
            (H z (n08ControlRestriction S u)) z.1 (0, (0, (u, 0)))) ∧
        (∀ s : ℕ, ∃ K : ℝ, 0 < K ∧
          ∀ z ∈ stateNeighborhood S C newBase η, ∀ b : ControlBanach,
          S.sourceGrading s (H z b) +
            heightPairGrading S s (G.G z (H z b)).1 + |(G.G z (H z b)).2| ≤
              K * (1 + stateGrading S (s + newLoss) (z.1 - C.referenceState) + |z.2|) * ‖b‖) ∧
        SmoothTameOn
          (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
          S.sourceGrading (sectorNeighborhood S newBase η η ×ˢ univ)
          (fun z : (StateDirections S × ℝ) × ControlBanach =>
            H (liftSectorParameter S C z.1) z.2) := by
  classical
  let H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source :=
    n08SectorControlColumn S Hraw
  let commonBase : ℕ := max base columnBase
  let ρ : ℝ := min ε (δ / 2)
  let V : Set (StateDirections S × ℝ) := sectorNeighborhood S commonBase ρ ρ
  have hρ : 0 < ρ := lt_min hε (half_pos hδ)
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρδ : 2 * ρ ≤ δ := by
    have h := min_le_right ε (δ / 2)
    dsimp only [ρ]
    linarith
  have hmap : MapsTo (liftSectorParameter S C) V
      {z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ} :=
    n08_sectorNeighborhood_maps_controlBall (le_max_right _ _) hρδ
  have hV : V ⊆ sectorNeighborhood S base ε ε :=
    n08_sectorNeighborhood_mono (le_max_left _ _) hρε hρε
  have hGv : LinearFamilyTame (pairGrading (sectorGrading S) realGrading)
      (pairGrading (heightPairGrading S) realGrading) S.sourceGrading V
      (fun z => (G.G (liftSectorParameter S C z)).toLinearMap) :=
    n08_linearFamilyTame_restrict hG hV
  have hHv := n08_sectorColumn_source_bound href Hraw hmap hcolumn
  refine n08_with_response_orders
    (n08_sectorColumn_response_orders (S := S) (C := C) (G := G)
      (V := V) (columnLoss := columnLoss) Hraw hGv hHv) ?_
  intro responseBase responseLoss hresponse
  let newBase : ℕ := max commonBase responseBase
  let newLoss : ℕ := max loss responseLoss
  let η : ℝ := min ρ (1 / 2)
  have hη : 0 < η := lt_min hρ (by norm_num)
  have hηρ : η ≤ ρ := min_le_left _ _
  have hηε : η ≤ ε := hηρ.trans hρε
  have hηδ : 2 * η ≤ δ := (mul_le_mul_of_nonneg_left hηρ (by norm_num)).trans hρδ
  have hηone : 2 * η ≤ 1 := by
    have h := min_le_right ρ (1 / 2 : ℝ)
    dsimp only [η]
    linarith
  have hnewV : sectorNeighborhood S newBase η η ⊆ V :=
    n08_sectorNeighborhood_mono (le_max_left _ _) hηρ hηρ
  have hnewMap : MapsTo (liftSectorParameter S C) (sectorNeighborhood S newBase η η)
      {z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ} :=
    fun _ hz => hmap (hnewV hz)
  refine ⟨newBase, newLoss, η, (le_max_left base columnBase).trans (le_max_left _ _),
    le_max_left _ _, hη, hηε, H,
    (fun z hz => n08SectorControlColumn_of_not_sector Hraw hz), ?_, ?_, ?_⟩
  · exact n08_sectorColumn_lineDeriv (S := S) (C := C) F Hraw
      (columnBase := columnBase) (newBase := newBase) (δ := δ) (η := η)
      ((le_max_right base columnBase).trans (le_max_left _ _)) hηδ hderiv
  · intro s
    refine n08_with_positive_response_bound (hresponse s) ?_
    intro K hK hKb
    exact ⟨K, hK, n08_sectorResponse_state_bound href Hraw hK
      (le_max_right _ _) (le_max_right _ _) hηone hnewV hKb⟩
  · exact n08SectorControlColumn_smoothTame href hsmooth hnewMap

/-- The control column is chosen together with one stronger state
neighborhood, its actual derivative, its sector smoothness, and the three
component bounds required by N08. The scalar inverse is unchanged. -/
theorem n08ControlInverseResponse_exists
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hG : ScalarInverseProperties D S C L G base ε) :
    ∃ newBase newLoss : ℕ, ∃ η : ℝ,
      base ≤ newBase ∧ loss ≤ newLoss ∧ 0 < η ∧ η ≤ ε ∧
      ∃ H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source,
        (∀ z, ¬ stateSector S z.1 → H z = 0) ∧
        (∀ z ∈ stateNeighborhood S C newBase η, stateSector S z.1 →
          ∀ u : CircleSpace S,
          HasProjectiveLineDerivAt
            (fun x => n08ActualScalarResidual hT hS hN (x, z.2))
            (H z (n08ControlRestriction S u)) z.1 (0, (0, (u, 0)))) ∧
        (∀ s : ℕ, ∃ K : ℝ, 0 < K ∧
          ∀ z ∈ stateNeighborhood S C newBase η, ∀ b : ControlBanach,
          S.sourceGrading s (H z b) +
            heightPairGrading S s (G.G z (H z b)).1 + |(G.G z (H z b)).2| ≤
              K * (1 + stateGrading S (s + newLoss) (z.1 - C.referenceState) + |z.2|) * ‖b‖) ∧
        SmoothTameOn
          (pairGrading (pairGrading (sectorGrading S) realGrading) controlGrading)
          S.sourceGrading (sectorNeighborhood S newBase η η ×ˢ univ)
          (fun z : (StateDirections S × ℝ) × ControlBanach =>
            H (liftSectorParameter S C z.1) z.2) := by
  refine n08_with_positive_column_witness
    (W := AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    (n08ActualControlColumn_exists hT hS hN) ?_
  intro columnBase columnLoss δ hδ Hraw hcolumnData
  exact n08ControlInverseResponse_of_column
    (D := D) (S := S) (C := C) (G := G)
    (base := base) (loss := loss) (ε := ε)
    (n08ActualScalarResidual hT hS hN)
    hN.2.1 hN.2.2.1 hG.2.2.1
    columnBase columnLoss δ hδ Hraw
    hcolumnData.1 hcolumnData.2.1 hcolumnData.2.2

end ContinuousFlexibility.Statements
