import ContinuousFlexibility.Radial.SelectedSideTransport

/-!
# The first cutoff layers and central column are separated on one geometry

The order comes from the actual gluing radii, retained by the constructor.
Any closed cutoff layer contained between the retained inner point and
the old cut lies strictly inside the matching interval. The full left
and right caps are separated from the central column as well.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem SeedRetainedPair.central_cones_order {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry}
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right) :
    P.pair.radiusL * P.left.inner < Γ.centralLeft ∧
      Γ.centralRight < P.pair.radiusR * P.right.inner := by
  rw [hleft, hright]
  constructor
  · exact ((mul_lt_mul_of_pos_left P.left.pure_cut P.pair.radiusL_pos).trans
      P.left_before).trans (exp_lt_exp.mpr (by linarith))
  · exact ((exp_lt_exp.mpr (by linarith : K.right < K.right + q + 4)).trans
      P.right_after).trans (mul_lt_mul_of_pos_left P.right.pure_cut
        (P.pair.radiusL_pos.trans_le P.pair.radius_order))

theorem SeedRetainedPair.first_matching_order {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S) (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry}
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right) :
    P.pair.radiusL * S.joinInner false S.chain.index < P.pair.radiusL * S.cut false S.chain.index ∧
    P.pair.radiusL * S.cut false S.chain.index < P.pair.radiusL * P.left.inner ∧
    P.pair.radiusL * P.left.inner < Γ.centralLeft ∧
    Γ.centralLeft < Γ.centralRight ∧
    Γ.centralRight < P.pair.radiusR * P.right.inner ∧
    P.pair.radiusR * P.right.inner < P.pair.radiusR * S.cut true S.chain.index ∧
    P.pair.radiusR * S.cut true S.chain.index < P.pair.radiusR * S.joinInner true S.chain.index := by
  have hL : S.entry false S.chain.index < S.joinInner false S.chain.index ∧
      S.joinInner false S.chain.index < S.cut false S.chain.index := by
    simpa only [Bool.false_eq_true, ite_false] using
      (hS.2.2.2.2.2 false S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.1
  have hR : S.cut true S.chain.index < S.joinInner true S.chain.index ∧
      S.joinInner true S.chain.index < S.entry true S.chain.index := by
    simpa only [ite_true] using
      (hS.2.2.2.2.2 true S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.1
  have hκR : 0 < P.pair.radiusR := P.pair.radiusL_pos.trans_le P.pair.radius_order
  have hcentral := P.central_cones_order hq hleft hright
  refine ⟨mul_lt_mul_of_pos_left hL.2 P.pair.radiusL_pos,
    mul_lt_mul_of_pos_left P.left.inner_order P.pair.radiusL_pos,
    hcentral.1, ?_, hcentral.2,
    mul_lt_mul_of_pos_left P.right.inner_order hκR,
    mul_lt_mul_of_pos_left hR.1 hκR⟩
  rw [hleft, hright]
  exact exp_lt_exp.mpr (K.left_neg.trans K.right_pos)

theorem connectedReference_column_in_central {Γ : ConnectedReferenceGeometry}
    (hΓ : Γ.Realizes) :
    tsupport (referenceColumn Γ.reference) ⊆ Ioo Γ.centralLeft Γ.centralRight := by
  rcases hΓ with ⟨_, _, _, _, hpatch, _, _, _, _, hsupp⟩
  have hturn : Γ.centralLeft < centralRadius (sqrt centralOscillatorA) :=
    hpatch.2.1.trans_le (strictMono_centralRadius.monotone
      (by linarith [sqrt_nonneg centralOscillatorA]))
  exact fun _ hr => ⟨hturn.trans (hsupp hr).1, (hsupp hr).2⟩

/-- Apply this to the physical `[a,2a]` layers once their retained-cone
containment is established. The conclusion concerns the same actual column. -/
theorem SeedRetainedPair.first_layers_separated {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (hS : IsSelectedTail S) (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    {JL JR : Set ℝ}
    (hJL : JL ⊆ Icc (P.pair.radiusL * S.cut false S.chain.index) (P.pair.radiusL * P.left.inner))
    (hJR : JR ⊆ Icc (P.pair.radiusR * P.right.inner) (P.pair.radiusR * S.cut true S.chain.index)) :
    let l := P.pair.radiusL * S.joinInner false S.chain.index
    let r := P.pair.radiusR * S.joinInner true S.chain.index
    l < r ∧ JL ⊆ Ioo l r ∧ JR ⊆ Ioo l r ∧
      tsupport (referenceColumn Γ.reference) ⊆ Ioo l r ∧
      Disjoint JL JR ∧ Disjoint JL (tsupport (referenceColumn Γ.reference)) ∧
      Disjoint JR (tsupport (referenceColumn Γ.reference)) ∧
      Disjoint (Icc l (P.pair.radiusL * P.left.inner))
        (tsupport (referenceColumn Γ.reference)) ∧
      Disjoint (Icc (P.pair.radiusR * P.right.inner) r)
        (tsupport (referenceColumn Γ.reference)) := by
  obtain ⟨hLC, hCI, hIL, hLH, hHR, hRC, hCJ⟩ :=
    P.first_matching_order hS hband hq hleft hright
  have hgap := hIL.trans (hLH.trans hHR)
  have hleftJoin : P.pair.radiusL * S.joinInner false S.chain.index < Γ.centralLeft :=
    hLC.trans (hCI.trans hIL)
  have hrightJoin : Γ.centralRight < P.pair.radiusR * S.joinInner true S.chain.index :=
    hHR.trans (hRC.trans hCJ)
  have hsupp := connectedReference_column_in_central hΓ
  refine ⟨hleftJoin.trans (hLH.trans hrightJoin), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hLC.trans_le (hJL hx).1,
      (hJL hx).2.trans_lt (hgap.trans (hRC.trans hCJ))⟩
  · intro x hx
    exact ⟨(hLC.trans (hCI.trans hgap)).trans_le (hJR hx).1,
      (hJR hx).2.trans_lt hCJ⟩
  · intro x hx
    exact ⟨hleftJoin.trans (hsupp hx).1, (hsupp hx).2.trans hrightJoin⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt hgap) ((hJR hy).1.trans (hJL hx).2)
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt ((hJL hx).2.trans_lt hIL)) (hsupp hy).1.le
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt ((hsupp hy).2.trans hHR)) (hJR hx).1
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt (hx.2.trans_lt hIL)) (hsupp hy).1.le
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt ((hsupp hy).2.trans hHR)) hx.1

end ContinuousFlexibility.Radial
