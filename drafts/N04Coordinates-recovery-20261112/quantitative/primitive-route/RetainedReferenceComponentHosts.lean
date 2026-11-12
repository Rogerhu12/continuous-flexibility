import ContinuousFlexibility.Analysis.RetainedReferenceComponentEnumeration
import ContinuousFlexibility.Analysis.MaterialCellHostIndex

/-!
# Actual hosts for the naturally enumerated retained components

At the midpoint of each actual Morse component, its old model cell and
its whole-component host overlap after the retained coordinate change.
The natural two-tail label and the original model cell have exactly the
same saturated index. The single central component costs one fixed
additional constant. No material cell or retained reference is changed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements

/-- Every genuine whole-component host obeys the additive index condition
for the natural enumeration of this same retained reference. -/
theorem retainedReference_enumeration_host_index
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ e : ℕ ≃ N01aNegativeComponent Γ.reference,
      ∀ host : ℕ → ℕ, (∀ m, (e m).interval ⊆ Γ.reference.cells (host m)) →
        ∃ B : ℝ, 0 < B ∧ ∀ m,
          |(Γ.reference.cellIndex (host m) : ℝ) - Γ.reference.cellIndex m| ≤ B := by
  obtain ⟨e, hzeroL, hzeroR, htailEndpoints⟩ :=
    retainedReference_natural_component_enumeration P hS hband hq hΓ hw hcoordinates
  refine ⟨e, ?_⟩
  intro host hhost
  obtain ⟨B₀, hB₀, hoverlap⟩ := materialCell_overlap_index_bound hT
  let D := S.family S.sigma
  let R (side : Bool) := if side then P.pair.radiusR else P.pair.radiusL
  let a (side : Bool) (k : ℕ) := S.chain.radius side (S.chain.index + k)
    (morseLeftTurn (morseChainA S.chain (S.chain.index + k))
      (morseChainB S.chain (S.chain.index + k)))
  let b (side : Bool) (k : ℕ) := S.chain.radius side (S.chain.index + k)
    (morseRightTurn (morseChainA S.chain (S.chain.index + k))
      (morseChainB S.chain (S.chain.index + k)))
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have horder := morseRealization_turning_component_order hreal
  obtain ⟨o, N, hN, hlabels, hindex, hcells, hlocal, hleft, hright, hfibers, ha, hb⟩ :=
    hcoordinates
  have hentry (side : Bool) :
      S.entry side S.chain.index = morseChainSeam S.chain side S.chain.index :=
    (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.2.1
  have htailBound (side : Bool) (k : ℕ) :
      |(Γ.reference.cellIndex (host (morseTailIndex side k)) : ℝ) -
        Γ.reference.cellIndex (morseTailIndex side k)| ≤ B₀ := by
    have hn : S.chain.index ≤ S.chain.index + k := Nat.le_add_right _ _
    have hreturn := morseRealization_model_return hreal hS.2.2.1 side hn
    have hmodel : NegativeRadialComponent D (a side k) (b side k) := hreturn.1
    let r := (a side k + b side k) / 2
    have hr : r ∈ Ioo (a side k) (b side k) := by
      dsimp only [r]
      constructor <;> linarith only [hmodel.2.1]
    obtain ⟨j, hjlabel, hrj⟩ := hreturn.2.2 r hr
    have hrTail : r ∈ radialTailInterval D side (S.entry side S.chain.index) := by
      rw [hentry]
      exact horder.2.2 side (S.chain.index + k) hn (Ioo_subset_Icc_self hr)
    have hR : 0 < R side := by
      cases side
      · exact P.pair.radiusL_pos
      · exact P.pair.radiusL_pos.trans_le P.pair.radius_order
    have hrComponent : R side * r ∈ (e (morseTailIndex side k)).interval := by
      change (e (morseTailIndex side k)).left < R side * r ∧
        R side * r < (e (morseTailIndex side k)).right
      rw [(htailEndpoints side k).1, (htailEndpoints side k).2]
      exact ⟨mul_lt_mul_of_pos_left hr.1 hR, mul_lt_mul_of_pos_left hr.2 hR⟩
    have hrCell : R side * r ∈ Γ.reference.cells j := by
      apply hcells j
      change o (R side * r) ∈ D.cells j
      cases side with
      | false =>
        change o (P.pair.radiusL * r) ∈ D.cells j
        rw [← hleft r hrTail.2.le, o.apply_symm_apply]
        exact hrj
      | true =>
        change o (P.pair.radiusR * r) ∈ D.cells j
        rw [← hright r hrTail.1.le, o.apply_symm_apply]
        exact hrj
    have hj : Γ.reference.cellIndex j =
        Γ.reference.cellIndex (morseTailIndex side k) := by
      have hj' : morseTwoTailAt S.chain.index (fun _ k => S.chain.index + k) j =
          S.chain.index + k := by
        simpa only [D, hlabels] using hjlabel
      simpa only [hindex, morseTwoTailAt_tail] using
        congrArg (fun n : ℕ => max n N) hj'
    have hb := hoverlap (host (morseTailIndex side k)) j (R side * r)
      (hhost _ hrComponent) hrCell
    simpa only [hj] using hb
  let B := max B₀ |(Γ.reference.cellIndex (host 0) : ℝ) - Γ.reference.cellIndex 0|
  refine ⟨B, hB₀.trans_le (le_max_left _ _), ?_⟩
  intro m
  cases m with
  | zero => exact le_max_right _ _
  | succ m =>
    let p := Equiv.boolProdNatEquivNat.symm m
    have hp : morseTailIndex p.1 p.2 = m + 1 := by
      unfold morseTailIndex
      rw [Prod.eta p]
      exact congrArg (· + 1) (Equiv.boolProdNatEquivNat.apply_symm_apply m)
    rw [← hp]
    exact (htailBound p.1 p.2).trans (le_max_left _ _)

end ContinuousFlexibility.Radial
