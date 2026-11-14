module

public import ContinuousFlexibility.Analysis.N03NegativePotentialAssembly
public import ContinuousFlexibility.Analysis.N03ControlledRootPhysicalJets

/-!
# Covering each actual negative half by fixed root bands and an interior

The two root collars are fixed before the state. Their quarter sections
leave an open middle interval. Actual disjointness identifies which
stored half contains every collar point, so no geometric graph or
unproved index-surjectivity assumption is used in combining the bounds.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem negative_cover_positiveJets_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {d e : ℕ} (hde : d ≤ e) {A B : ℕ → ℝ}
    (hA : ∀ n, 0 ≤ A n) (hAB : ∀ n, A n ≤ B n)
    {z : E} {F : PolarPoint → PolarPoint} {q : PolarPoint}
    (hF : ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F q‖ ≤
      A n * (1 + p (n + d) z)) :
    ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F q‖ ≤
      B n * (1 + p (n + e) z) := by
  intro n hn
  exact (hF n hn).trans (mul_le_mul (hAB n)
    (add_le_add (le_refl (1 : ℝ)) (hp (Nat.add_le_add_left hde n) z))
    (add_nonneg zero_le_one (apply_nonneg _ _)) ((hA n).trans (hAB n)))

private theorem negative_cover_of_families
    {E Z : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    (shift : Z → E) (states : Set Z) (sector : Z → Prop)
    (l r : ℝ) (roots signs : Bool → ℝ)
    (hrootL : roots false = l) (hrootR : roots true = r)
    (hsignL : signs false = 1) (hsignR : signs true = -1)
    (index : Bool → ℕ) (F : Z → ℕ → PolarPoint → PolarPoint)
    (H : Z → ℕ → PolarPoint → ℝ) (Ω : Z → ℕ → Set PolarPoint)
    {rootLoss middleLoss : ℕ}
    (w κ : Bool → ℝ) (A : Bool → ℕ → ℝ)
    (hw : ∀ side, 0 < w side) (hκ : ∀ side, 0 < κ side)
    (hApos : ∀ side n, 0 < A side n)
    (hdisjoint : ∀ z ∈ states, sector z →
      Pairwise (fun i j => Disjoint (Ω z i) (Ω z j)))
    (hcomponent : ∀ z ∈ states, sector z → ∀ side : Bool,
      ∀ q ∈ Ω z (index side), q.1 ∈ Ioo l r)
    (hroot : ∀ e : Bool, ∀ z ∈ states, sector z →
      ∀ x ∈ Icc (0 : ℝ) (w e), ∀ θ : ℝ,
      let q : PolarPoint := (roots e + signs e * x, θ)
      (0 < x → q ∈ Ω z (index e)) ∧
        κ e ≤ |planeJacobian (F z (index e)) q| ∧
        RootPhysicalFieldJetBound p rootLoss (A e) (shift z)
          (F z (index e)) (H z (index e)) q)
    (κM : ℝ) (M : ℕ → ℝ) (hκM : 0 < κM) (hM : ∀ n, 0 < M n)
    (hmiddle : ∀ z ∈ states, sector z → ∀ side : Bool, ∀ q ∈ Ω z (index side),
      q.1 ∈ Ioo (l + w false / 4) (r - w true / 4) →
        κM ≤ |planeJacobian (F z (index side)) q| ∧
        PointwiseMaterialJetBound p middleLoss M (shift z) (H z (index side)) q ∧
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (F z (index side)) q‖ ≤
          M n * (1 + p (n + middleLoss) (shift z))) :
    ∃ κ' : ℝ, ∃ B : ℕ → ℝ, 0 < κ' ∧ (∀ n, 0 < B n) ∧
      ∀ z ∈ states, sector z → ∀ side : Bool,
      let i := index side
      ∀ q ∈ Ω z i,
        κ' ≤ |planeJacobian (F z i) q| ∧
        PointwiseMaterialJetBound p (max rootLoss middleLoss) B (shift z) (H z i) q ∧
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (F z i) q‖ ≤
          B n * (1 + p (n + max rootLoss middleLoss) (shift z)) := by
  let κ' := min (κ false) (min (κ true) κM)
  let B (n : ℕ) : ℝ := 1 + A false n + A true n + M n
  have hB (n : ℕ) : 0 < B n := by
    dsimp only [B]
    linarith [hApos false n, hApos true n, hM n]
  have hAB (side : Bool) (n : ℕ) : A side n ≤ B n := by
    cases side <;> dsimp only [B] <;>
      linarith [hApos false n, hApos true n, hM n]
  have hMB (n : ℕ) : M n ≤ B n := by
    dsimp only [B]
    linarith [hApos false n, hApos true n]
  refine ⟨κ', B, lt_min (hκ false) (lt_min (hκ true) hκM), hB, ?_⟩
  intro z hz hs side
  dsimp only
  intro q hq
  let i := index side
  have hqN : q.1 ∈ Ioo l r := hcomponent z hz hs side q hq
  have hrootUse (e : Bool) (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) (w e))
      (he : (roots e + signs e * x, q.2) = q) :
      κ e ≤ |planeJacobian (F z i) q| ∧
        PointwiseMaterialJetBound p
          rootLoss (A e) (shift z) (H z i) q ∧
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (F z i) q‖ ≤
          A e n * (1 + p (n + rootLoss)
            (shift z)) := by
    have hr := hroot e z hz hs x ⟨hx.1.le, hx.2⟩ q.2
    dsimp only at hr
    rw [he] at hr
    have hi : i = index e := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisjoint z hz hs hne)
        hq (hr.1 hx.1)
    rw [hi]
    obtain ⟨_hF, _hH, _hpos, hFjets, hHjets, _hinv⟩ := hr.2.2
    exact ⟨hr.2.1, hHjets, hFjets⟩
  have hfinishRoot (e : Bool)
      (he : κ e ≤ |planeJacobian (F z i) q| ∧
        PointwiseMaterialJetBound p
          rootLoss (A e) (shift z) (H z i) q ∧
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (F z i) q‖ ≤
          A e n * (1 + p (n + rootLoss)
            (shift z))) :
      κ' ≤ |planeJacobian (F z i) q| ∧
        PointwiseMaterialJetBound p
          (max rootLoss middleLoss) B (shift z) (H z i) q ∧
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (F z i) q‖ ≤
          B n * (1 + p
            (n + max rootLoss middleLoss) (shift z)) := by
    have hk : κ' ≤ κ e := by
      cases e
      · exact min_le_left _ _
      · exact (min_le_right (κ false) (min (κ true) κM)).trans (min_le_left _ _)
    exact ⟨hk.trans he.1,
      he.2.1.mono hp (le_max_left _ _) (fun n => (hApos e n).le) (hAB e),
      negative_cover_positiveJets_mono hp (le_max_left _ _)
        (fun n => (hApos e n).le) (hAB e) he.2.2⟩
  by_cases hleft : q.1 ≤ l + w false / 2
  · apply hfinishRoot false
    apply hrootUse false (q.1 - l)
    · exact ⟨sub_pos.mpr hqN.1, by linarith [hw false]⟩
    · ext <;> simp only [hrootL, hsignL, one_mul] <;> ring
  by_cases hright : r - w true / 2 ≤ q.1
  · apply hfinishRoot true
    apply hrootUse true (r - q.1)
    · exact ⟨sub_pos.mpr hqN.2, by linarith [hw true]⟩
    · ext <;> simp only [hrootR, hsignR, neg_one_mul] <;> ring
  have hmiddlePoint := hmiddle z hz hs side q hq
    ⟨by linarith [hw false], by linarith [hw true]⟩
  have hk : κ' ≤ κM := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨hk.trans hmiddlePoint.1,
    hmiddlePoint.2.1.mono hp (le_max_right _ _) (fun n => (hM n).le) hMB,
    negative_cover_positiveJets_mono hp (le_max_right _ _)
      (fun n => (hM n).le) hMB hmiddlePoint.2.2⟩


private theorem n03_negative_cover_component
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hcut : CanonicalCutGeometry S C K base ε) (m : ℕ) :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ side : Bool,
      ∀ q ∈ physicalPieceOpen S K z
        (if side then (K.cutPair m).2 else (K.cutPair m).1),
        q.1 ∈ Ioo (C.left m) (C.right m) := by
  intro z hz hs side q hq
  have hu : q ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
      physicalPieceOpen S K z (K.cutPair m).2 := by
    cases side with
    | false => exact Or.inl hq
    | true => exact Or.inr hq
  rw [(hcut.2 z hz hs m).2.2.2.1] at hu
  exact hu.1.1

private theorem n03_negative_cover_root_data
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base rootLoss : ℕ} {ε : ℝ} {m : ℕ}
    {w κ : Bool → ℝ} {A : Bool → ℕ → ℝ}
    (hroot : ∀ side, N03RootPhysicalFieldFamily D S C K base rootLoss ε
      m side (w side) (κ side) (A side)) :
    ∀ e : Bool, ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ x ∈ Icc (0 : ℝ) (w e), ∀ θ : ℝ,
      let q : PolarPoint := (n01ComponentRoot C m e + n01ComponentRootOrientation e * x, θ)
      (0 < x → q ∈ physicalPieceOpen S K z
        (if e then (K.cutPair m).2 else (K.cutPair m).1)) ∧
        κ e ≤ |planeJacobian
          (K.chart z (if e then (K.cutPair m).2 else (K.cutPair m).1)) q| ∧
        RootPhysicalFieldJetBound (pairGrading (stateGrading S) realGrading)
          rootLoss (A e) (z - (C.referenceState, 0))
          (K.chart z (if e then (K.cutPair m).2 else (K.cutPair m).1))
          (K.height z (if e then (K.cutPair m).2 else (K.cutPair m).1)) q := by
  intro e z hz hs x hx θ
  exact (hroot e z hz hs x hx θ).2

theorem n03_negativePhysical_component_of_root_and_middle
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base rootLoss middleLoss : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε) (m : ℕ)
    (w κ : Bool → ℝ) (A : Bool → ℕ → ℝ)
    (hw : ∀ side, 0 < w side) (hκ : ∀ side, 0 < κ side)
    (hApos : ∀ side n, 0 < A side n)
    (hroot : ∀ side, N03RootPhysicalFieldFamily D S C K base rootLoss ε
      m side (w side) (κ side) (A side))
    (κM : ℝ) (M : ℕ → ℝ) (hκM : 0 < κM) (hM : ∀ n, 0 < M n)
    (hmiddle : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ side : Bool, ∀ q ∈ physicalPieceOpen S K z
        (if side then (K.cutPair m).2 else (K.cutPair m).1),
      q.1 ∈ Ioo (C.left m + w false / 4) (C.right m - w true / 4) →
        κM ≤ |planeJacobian
          (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1)) q| ∧
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
          middleLoss M (z - (C.referenceState, 0))
          (K.height z (if side then (K.cutPair m).2 else (K.cutPair m).1)) q ∧
        ∀ n : ℕ, 1 ≤ n →
          ‖iteratedFDeriv ℝ n
            (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1)) q‖ ≤
            M n * (1 + pairGrading (stateGrading S) realGrading (n + middleLoss)
              (z - (C.referenceState, 0)))) :
    ∃ κ' : ℝ, ∃ B : ℕ → ℝ, 0 < κ' ∧ (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ side : Bool,
      let i := if side then (K.cutPair m).2 else (K.cutPair m).1
      ∀ q ∈ physicalPieceOpen S K z i,
        κ' ≤ |planeJacobian (K.chart z i) q| ∧
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
          (max rootLoss middleLoss) B (z - (C.referenceState, 0)) (K.height z i) q ∧
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (K.chart z i) q‖ ≤
          B n * (1 + pairGrading (stateGrading S) realGrading
            (n + max rootLoss middleLoss) (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  exact negative_cover_of_families
    (E := AnnularState S × ℝ) (Z := AnnularState S × ℝ)
    (p := pairGrading (stateGrading S) realGrading)
    (rootLoss := rootLoss) (middleLoss := middleLoss) hp
    (fun z => z - (C.referenceState, 0)) (stateNeighborhood S C base ε)
    (fun z => stateSector S z.1) (C.left m) (C.right m)
    (n01ComponentRoot C m) n01ComponentRootOrientation rfl rfl rfl rfl
    (fun side => if side then (K.cutPair m).2 else (K.cutPair m).1)
    K.chart K.height (physicalPieceOpen S K) w κ A hw hκ hApos
    (fun z hz hs => canonicalPhysicalPieces_pairwise_disjoint hA hz hs)
    (n03_negative_cover_component hcut m)
    (n03_negative_cover_root_data (D := D) (S := S) (C := C) (K := K)
      (base := base) (rootLoss := rootLoss) (ε := ε) (m := m) hroot)
    κM M hκM hM hmiddle

end ContinuousFlexibility.Analysis
