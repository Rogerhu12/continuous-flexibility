module

public import ContinuousFlexibility.Analysis.RetainedNegativeComponentIdentification
public import ContinuousFlexibility.Analysis.MorseRealizationComponentOrder
public import ContinuousFlexibility.Analysis.N01aNegativeComponentGeometry

/-!
# The natural component enumeration of the same retained reference

The actual central interval occupies zero. Each remaining index is the
existing Bool-times-Nat code of an actual scaled Morse component. The
realized join order proves injectivity, and the retained profile
classification proves surjectivity. No reindexing of material cells or
replacement of the retained reference is performed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

private theorem twoTailAt_injective_of_separated
    {α : Type*} (middle : α) (tail : Bool → ℕ → α)
    (hneq : ∀ side k, tail side k ≠ middle)
    (hinj : Function.Injective (fun p : Bool × ℕ => tail p.1 p.2)) :
    Function.Injective (morseTwoTailAt middle tail) := by
  intro m n he
  cases m with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => exact False.elim (hneq _ _ he.symm)
  | succ m =>
    cases n with
    | zero => exact False.elim (hneq _ _ he)
    | succ n =>
      have hp : Equiv.boolProdNatEquivNat.symm m =
          Equiv.boolProdNatEquivNat.symm n := hinj he
      exact congrArg Nat.succ (Equiv.boolProdNatEquivNat.symm.injective hp)

/-- The same retained reference admits the central/two-tail enumeration
whose model number agrees exactly with its original material labels. -/
theorem retainedReference_natural_component_enumeration
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ) :
    ∃ e : ℕ ≃ N01aNegativeComponent Γ.reference,
      (e 0).left = centralRadius (-sqrt centralOscillatorA) ∧
      (e 0).right = centralRadius (sqrt centralOscillatorA) ∧
      ∀ side : Bool, ∀ k : ℕ,
        (e (morseTailIndex side k)).left =
          (if side then P.pair.radiusR else P.pair.radiusL) *
            S.chain.radius side (S.chain.index + k)
              (morseLeftTurn (morseChainA S.chain (S.chain.index + k))
                (morseChainB S.chain (S.chain.index + k))) ∧
        (e (morseTailIndex side k)).right =
          (if side then P.pair.radiusR else P.pair.radiusL) *
            S.chain.radius side (S.chain.index + k)
              (morseRightTurn (morseChainA S.chain (S.chain.index + k))
                (morseChainB S.chain (S.chain.index + k))) := by
  classical
  let D := S.family S.sigma
  let G := P.toEntryPair hS hband
  have hGL : G.radiusL = P.pair.radiusL := rfl
  have hGR : G.radiusR = P.pair.radiusR := rfl
  have hGp : G.profile = P.pair.profile := rfl
  let R (side : Bool) := if side then G.radiusR else G.radiusL
  let a (side : Bool) (k : ℕ) := S.chain.radius side (S.chain.index + k)
    (morseLeftTurn (morseChainA S.chain (S.chain.index + k))
      (morseChainB S.chain (S.chain.index + k)))
  let b (side : Bool) (k : ℕ) := S.chain.radius side (S.chain.index + k)
    (morseRightTurn (morseChainA S.chain (S.chain.index + k))
      (morseChainB S.chain (S.chain.index + k)))
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hE : ContDiff ℝ ∞ Γ.reference.w := hΓ.2.1.choose_spec.1.2.2.1.1
  have horder := morseRealization_turning_component_order hreal
  have hcoordinates' := hcoordinates
  obtain ⟨o, N, hN, hlabels, hindex, hcells, hlocal, hleft, hright, hfibers, ha, hb⟩ :=
    hcoordinates'
  have hentry (side : Bool) :
      S.entry side S.chain.index = morseChainSeam S.chain side S.chain.index :=
    (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.2.1
  have hc : S.entry false S.chain.index ∈ radialCore D :=
    (hS.2.2.2.2.2 false S.chain.index 2 le_rfl (by decide) hband).2.1
  have hd : S.entry true S.chain.index ∈ radialCore D :=
    (hS.2.2.2.2.2 true S.chain.index 2 le_rfl (by decide) hband).2.1
  have hRR : 0 < G.radiusR := G.radiusL_pos.trans_le G.radius_order
  have hDb : 0 < D.b := hreal.geometry.1.trans hreal.geometry.2.1
  have hleftCore (r : ℝ) (hr : r ∈ Ioo D.a (S.entry false S.chain.index)) :
      G.radiusL * r ∈ radialCore Γ.reference := by
    change Γ.reference.a < G.radiusL * r ∧ G.radiusL * r < Γ.reference.b
    rw [ha, hb]
    exact ⟨mul_lt_mul_of_pos_left hr.1 G.radiusL_pos,
      (mul_lt_mul_of_pos_left (hr.2.trans hc.2) G.radiusL_pos).trans_le
        (mul_le_mul_of_nonneg_right G.radius_order hDb.le)⟩
  have hrightCore (r : ℝ) (hr : r ∈ Ioo (S.entry true S.chain.index) D.b) :
      G.radiusR * r ∈ radialCore Γ.reference := by
    change Γ.reference.a < G.radiusR * r ∧ G.radiusR * r < Γ.reference.b
    rw [ha, hb]
    exact ⟨(mul_le_mul_of_nonneg_right G.radius_order hreal.geometry.1.le).trans_lt
      (mul_lt_mul_of_pos_left (hd.1.trans hr.1) hRR),
      mul_lt_mul_of_pos_left hr.2 hRR⟩
  have hclosed (side : Bool) (k : ℕ) : Icc (a side k) (b side k) ⊆
      radialTailInterval D side (S.entry side S.chain.index) := by
    rw [hentry]
    exact horder.2.2 side (S.chain.index + k) (Nat.le_add_right _ _)
  have hmodel (side : Bool) (k : ℕ) : NegativeRadialComponent D (a side k) (b side k) :=
    (morseRealization_model_return hreal hS.2.2.1 side
      (n := S.chain.index + k) (Nat.le_add_right _ _)).1
  have hscaled (side : Bool) (k : ℕ) :
      NegativeRadialComponent Γ.reference (R side * a side k) (R side * b side k) := by
    have hl := hclosed side k (left_mem_Icc.mpr (hmodel side k).2.1.le)
    have hr := hclosed side k (right_mem_Icc.mpr (hmodel side k).2.1.le)
    cases side with
    | false =>
      exact (negativeRadialComponent_travel_of_tail_identity
        (E := Γ.reference) (R := G.radiusL) (H := G.heightL)
        G.radiusL_pos G.heightL_pos (hmodel false k)
        (hleftCore _ hl).1 (hleftCore _ hr).2 hreal.geometry.2.2.1.1 hE
        (hclosed false k) (fun r hr => by rw [hw]; exact (G.left_tail r hr).1)).1
    | true =>
      exact (negativeRadialComponent_travel_of_tail_identity
        (E := Γ.reference) (R := G.radiusR) (H := G.heightR)
        hRR G.heightR_pos (hmodel true k)
        (hrightCore _ hl).1 (hrightCore _ hr).2 hreal.geometry.2.2.1.1 hE
        (hclosed true k) (fun r hr => by rw [hw]; exact (G.right_tail r hr).1)).1
  have hcentral : NegativeRadialComponent Γ.reference
      (centralRadius (-sqrt centralOscillatorA)) (centralRadius (sqrt centralOscillatorA)) := by
    simpa only [NegativeRadialComponent, ha, hb, hw, hGL, hGR, hGp] using
      (G.central_model_return hq hc hd).1
  let J₀ : N01aNegativeComponent Γ.reference :=
    ⟨(centralRadius (-sqrt centralOscillatorA), centralRadius (sqrt centralOscillatorA)), hcentral⟩
  let J (side : Bool) (k : ℕ) : N01aNegativeComponent Γ.reference :=
    ⟨(R side * a side k, R side * b side k), hscaled side k⟩
  have hsepL (k : ℕ) : (J false k).left < J₀.left := by
    have hl := (hclosed false k (left_mem_Icc.mpr (hmodel false k).2.1.le)).2
    have hturn : exp K.left < centralRadius (-sqrt centralOscillatorA) :=
      (lt_log_iff_exp_lt (centralRadius_pos _)).mp K.left_turn
    exact ((mul_lt_mul_of_pos_left hl G.radiusL_pos).trans G.left_entry).trans
      ((exp_lt_exp.mpr (by linarith only [hq])).trans hturn)
  have hsepR (k : ℕ) : J₀.right < (J true k).left := by
    have hl := (hclosed true k (left_mem_Icc.mpr (hmodel true k).2.1.le)).1
    have hturn : centralRadius (sqrt centralOscillatorA) < exp K.right :=
      (log_lt_iff_lt_exp (centralRadius_pos _)).mp K.right_turn
    exact (hturn.trans ((exp_lt_exp.mpr (by linarith only [hq])).trans G.right_entry)).trans
      (mul_lt_mul_of_pos_left hl hRR)
  have hneq (side : Bool) (k : ℕ) : J side k ≠ J₀ := by
    intro he
    have hl := congrArg N01aNegativeComponent.left he
    cases side with
    | false => exact (hsepL k).ne hl
    | true => exact (hcentral.2.1.trans (hsepR k)).ne hl.symm
  have hinj : Function.Injective (fun p : Bool × ℕ => J p.1 p.2) := by
    rintro ⟨side, k⟩ ⟨side', j⟩ he
    have hl := congrArg N01aNegativeComponent.left he
    cases side <;> cases side'
    · change G.radiusL * a false k = G.radiusL * a false j at hl
      exact Prod.ext rfl (horder.1.injective (mul_left_cancel₀ G.radiusL_pos.ne' hl))
    · exact False.elim (((hsepL k).trans (hcentral.2.1.trans (hsepR j))).ne hl)
    · exact False.elim (((hsepL j).trans (hcentral.2.1.trans (hsepR k))).ne hl.symm)
    · change G.radiusR * a true k = G.radiusR * a true j at hl
      exact Prod.ext rfl (horder.2.1.injective (mul_left_cancel₀ hRR.ne' hl))
  let f : ℕ → N01aNegativeComponent Γ.reference := morseTwoTailAt J₀ J
  have hsurj : Function.Surjective f := by
    intro Q
    rcases retainedReference_negative_component_identification P hS hband hq hΓ hw
        hcoordinates Q.property with hmid | htail
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      exact Prod.ext hmid.1.symm hmid.2.symm
    · obtain ⟨side, n, hn, hl, hr, hclosedOld⟩ := htail
      refine ⟨morseTailIndex side (n - S.chain.index), ?_⟩
      change morseTwoTailAt J₀ J (morseTailIndex side (n - S.chain.index)) = Q
      rw [morseTwoTailAt_tail]
      apply Subtype.ext
      apply Prod.ext
      · simpa only [J, a, R, Nat.add_sub_of_le hn, hGL, hGR, N01aNegativeComponent.left]
          using hl.symm
      · simpa only [J, b, R, Nat.add_sub_of_le hn, hGL, hGR, N01aNegativeComponent.right]
          using hr.symm
  let e : ℕ ≃ N01aNegativeComponent Γ.reference :=
    Equiv.ofBijective f ⟨twoTailAt_injective_of_separated J₀ J hneq hinj, hsurj⟩
  refine ⟨e, rfl, rfl, ?_⟩
  intro side k
  change (morseTwoTailAt J₀ J (morseTailIndex side k)).left = _ ∧
    (morseTwoTailAt J₀ J (morseTailIndex side k)).right = _
  rw [morseTwoTailAt_tail]
  exact ⟨rfl, rfl⟩

end ContinuousFlexibility.Radial
