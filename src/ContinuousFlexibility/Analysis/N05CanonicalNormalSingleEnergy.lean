module

public import ContinuousFlexibility.Analysis.N05CanonicalSourceSingleJetBounds
public import ContinuousFlexibility.Radial.R11bAngularFrequencySource

/-!
# The actual single-source energies required by first-normal estimates

All corrected angular jets use the same actual compatibility scalar.
Their existing same-endpoint bounds control the first-normal base energy
and every consecutive pair of source jets, with one coefficient power
chosen before the retained angular order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Radial
open scoped BigOperators

theorem n05_canonicalNormalSingle_source_energy_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε σ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) (hσ : 0 < σ) (M : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (v : n05CanonicalClosedSubmodule S K (s + 1)),
      let F := n05CanonicalNormalizedSource D S C K (Pi.single m (v.val m 0))
      let d := n05CanonicalNormalizedSingleJetSource D S C K (s + 1) m v
      let first : Fin (s + 1 + 1) := ⟨1, by omega⟩
      let W := radialE (D.cellIndex (K.cell m)) ^ A *
        Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2
      SourceMember D σ M F ∧
      (∀ i, SourceDerivativeMember D σ M (d i) ∧
        n05_weakReferenceAngularJet D F.1 (d i) i.val) ∧
      sourceNormSquare D σ M F + sourceNormSquare D σ M (d first, 0) ≤ B * W ∧
      ∀ j : Fin (s + 1),
        sourceNormSquare D σ M (d j.castSucc, 0) +
          sourceNormSquare D σ M (d j.succ, 0) + (2 : ℝ) ^ (2 * j.val) *
            (sourceNormSquare D σ M F + sourceNormSquare D σ M (d first, 0)) ≤ B * W := by
  obtain ⟨A, hA, hs⟩ :=
    n05_canonicalNormalizedSingleJet_reference_bound hD hT hS h hcoordinates hσ M
  refine ⟨A, hA, fun s => ?_⟩
  obtain ⟨C0, hC0, hbound⟩ := hs (s + 1)
  let Z : ℝ := ∑ j : Fin (s + 1), (2 : ℝ) ^ (2 * j.val)
  have hterm (j : Fin (s + 1)) : 0 ≤ (2 : ℝ) ^ (2 * j.val) := by positivity
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun j _ => hterm j)
  have hpow (j : Fin (s + 1)) : (2 : ℝ) ^ (2 * j.val) ≤ Z :=
    Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ j)
  refine ⟨C0 * (2 + 2 * Z), by positivity, fun m v => ?_⟩
  dsimp only
  let F := n05CanonicalNormalizedSource D S C K (Pi.single m (v.val m 0))
  let d := n05CanonicalNormalizedSingleJetSource D S C K (s + 1) m v
  let first : Fin (s + 1 + 1) := ⟨1, by omega⟩
  let W := radialE (D.cellIndex (K.cell m)) ^ A *
    Real.exp (2 * σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ ^ 2
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hF : SourceMember D σ M F := (hbound m v 0).1
  have hFn : 0 ≤ sourceNormSquare D σ M F := sourceNormSquare_nonneg hab hF
  have hEm : 0 < radialE (D.cellIndex (K.cell m)) := Real.exp_pos _
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hdn (i : Fin (s + 1 + 1)) : 0 ≤ sourceNormSquare D σ M (d i, 0) :=
    r11b_sourceNormSquare_nonneg hab σ M (d i, 0)
  have hc (i : Fin (s + 1 + 1)) : sourceNormSquare D σ M (d i, 0) +
      (2 : ℝ) ^ (2 * i.val) * sourceNormSquare D σ M F ≤ C0 * W :=
    (hbound m v i).2.2.2.trans_eq (by dsimp only [W]; ring)
  have hFb : sourceNormSquare D σ M F ≤ C0 * W := by
    have hz := hc 0
    simp only [Fin.val_zero, Nat.mul_zero, pow_zero, one_mul] at hz
    linarith only [hz, hdn 0]
  have hdb (i : Fin (s + 1 + 1)) : sourceNormSquare D σ M (d i, 0) ≤ C0 * W := by
    linarith only [hc i, mul_nonneg (show 0 ≤ (2 : ℝ) ^ (2 * i.val) by positivity) hFn]
  have hbase : sourceNormSquare D σ M F + sourceNormSquare D σ M (d first, 0) ≤
      2 * C0 * W := (add_le_add hFb (hdb first)).trans_eq (by ring)
  have hbaseNonneg : 0 ≤ sourceNormSquare D σ M F + sourceNormSquare D σ M (d first, 0) :=
    add_nonneg hFn (hdn first)
  refine ⟨hF, fun i => ⟨(hbound m v i).2.1, (hbound m v i).2.2.1⟩, ?_, fun j => ?_⟩
  · exact hbase.trans (mul_le_mul_of_nonneg_right
      (show 2 * C0 ≤ C0 * (2 + 2 * Z) by nlinarith only [mul_nonneg hC0.le hZ]) hW)
  · have hlow : (2 : ℝ) ^ (2 * j.val) *
        (sourceNormSquare D σ M F + sourceNormSquare D σ M (d first, 0)) ≤
        Z * (2 * C0 * W) := mul_le_mul (hpow j) hbase hbaseNonneg hZ
    calc
      _ ≤ C0 * W + C0 * W + Z * (2 * C0 * W) :=
        add_le_add (add_le_add (hdb j.castSucc) (hdb j.succ)) hlow
      _ = _ := by ring

end ContinuousFlexibility.Statements
