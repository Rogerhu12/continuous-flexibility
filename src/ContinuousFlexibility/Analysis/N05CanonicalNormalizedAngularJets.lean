import ContinuousFlexibility.Analysis.N05CanonicalSourceWeakClosure
import ContinuousFlexibility.Analysis.N05CanonicalInverseDefinition

/-!
# Angular jets of the actual normalized canonical source

The compatibility scalar is the original physical integral. The corrected
jet subtracts that same scalar times the actual angular derivative of ψ.
Every finite family has a source bound at the same preassigned material
order; only its norm constant depends on the retained angular order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open scoped Topology BigOperators

theorem n05_sourceDerivativeMember_sub_const_mul_bound
    {D : ReferenceData} (hab : D.a ≤ D.b) {γ M : ℝ} {f g : PolarPoint → ℝ}
    (hf : SourceDerivativeMember D γ M f) (hg : SourceDerivativeMember D γ M g) (c : ℝ) :
    SourceDerivativeMember D γ M (fun p => f p - c * g p) ∧
      sourceNormSquare D γ M ((fun p => f p - c * g p), 0) ≤
        2 * (sourceNormSquare D γ M (f, 0) + c ^ 2 * sourceNormSquare D γ M (g, 0)) := by
  have hscaled := hg.1.const_mul (-c)
  have hscaledSum := sourceCellSquare_summable_const_mul hg.2 (-c)
  have hs := sourceCellSquare_summable_add hab hf.1 hscaled hf.2 hscaledSum
  have hb := hs.tsum_le_tsum
    (fun m => sourceCellSquare_add_le hab γ M m hf.1 hscaled)
    ((hf.2.add hscaledSum).mul_left 2)
  have hsumScaled : (∑' m, sourceCellSquare D γ M (fun p => (-c) * g p) m) =
      c ^ 2 * ∑' m, sourceCellSquare D γ M g m := by
    simp_rw [sourceCellSquare_const_mul, neg_sq]
    exact tsum_mul_left
  rw [tsum_mul_left, hf.2.tsum_add hscaledSum, hsumScaled] at hb
  have he : (fun p => f p - c * g p) = (fun p => f p + (-c) * g p) := by
    funext p
    ring
  refine ⟨?_, ?_⟩
  · rw [he]
    exact ⟨hf.1.add hscaled, hs⟩
  · simp only [sourceNormSquare, zero_pow (by decide : 2 ≠ 0), zero_add]
    rw [he]
    exact hb

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hV : IsVolumeModel T S K V)
  {γw γ : ℝ} (hγw : 0 < γw) (hgap : γw < γ) (t M : ℝ)

include h hcoordinates hD hT hV hγw hgap M in
/-- The actual compatibility scalar has a bound independent of the
number of retained angular jets. -/
theorem n05CanonicalAuxiliaryScalar_volume_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (s : ℕ) (v : V.level γ t s),
      n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v) ^ 2 ≤ A * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05CanonicalJetSource_reference_bound h hcoordinates hD hT hγw.le hgap t M
  obtain ⟨Q, hQ, hscalar⟩ := n05_referenceAuxiliaryScalar_square_bound hD hγw M
  refine ⟨Q * B, mul_pos hQ hB, fun s v => ?_⟩
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hzero := n05CanonicalJetSource_zero_ae h hcoordinates hV γ t s v
  have hcell := RadialCellIntegrable.congr_ae (hb s 0 v.val).1.1 hzero
  have he (m : ℕ) : sourceCellSquare D γw M
      (n05CanonicalJetSource T S C K γ t s 0 v.val) m =
        sourceCellSquare D γw M (n05CanonicalSourceLift S C K (V.forget γ t s v)) m := by
    unfold sourceCellSquare
    rw [referenceCellSquare_congr_ae hab m (hb s 0 v.val).1.1 hzero]
  have hf : SourceDerivativeMember D γw M
      (n05CanonicalSourceLift S C K (V.forget γ t s v)) :=
    ⟨hcell, (hb s 0 v.val).1.2.congr he⟩
  have heNorm : sourceNormSquare D γw M
      (n05CanonicalSourceLift S C K (V.forget γ t s v), 0) =
        sourceNormSquare D γw M (n05CanonicalJetSource T S C K γ t s 0 v.val, 0) := by
    unfold sourceNormSquare
    rw [tsum_congr (fun m => (he m).symm)]
  have hnorm : sourceNormSquare D γw M
      (n05CanonicalSourceLift S C K (V.forget γ t s v), 0) ≤ B * ‖v‖ ^ 2 := by
    rw [heNorm]
    exact (hb s 0 v.val).2
  have haux : n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v) ^ 2 ≤
      Q * sourceNormSquare D γw M
        (n05CanonicalSourceLift S C K (V.forget γ t s v), 0) := by
    simpa only [n05CanonicalAuxiliaryScalar, sourceNormSquare,
      zero_pow (by decide : 2 ≠ 0), zero_add] using
      hscalar _ hf
  exact haux.trans ((mul_le_mul_of_nonneg_left hnorm hQ.le).trans_eq (by ring))

def n05CanonicalNormalizedJetSource (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (V : VolumeModelData S K) (γ t : ℝ) (s : ℕ) (j : Fin (s + 1))
    (v : V.level γ t s) : PolarPoint → ℝ := fun p =>
  n05CanonicalJetSource T S C K γ t s j v.val p -
    n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v) *
      mixedDerivative 0 j.val ((S.height (3 / 4 : ℝ)).decode S.psi) p

include h hcoordinates hD hT hV hγw hgap in
/-- All corrected jets belong to the fixed reference source space and
differentiate the very normalized source used by the global inverse. -/
theorem n05CanonicalNormalizedSource_allAngularJets
    (hS : IsPhysicalSpaces D T S) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (v : V.level γ t s) (j : Fin (s + 1)),
      SourceDerivativeMember D γw M (n05CanonicalNormalizedJetSource D T S C K V γ t s j v) ∧
      sourceNormSquare D γw M (n05CanonicalNormalizedJetSource D T S C K V γ t s j v, 0) ≤
        B * ‖v‖ ^ 2 ∧
      n05_weakReferenceAngularJet D
        (n05CanonicalNormalizedSource D S C K (V.forget γ t s v)).1
        (n05CanonicalNormalizedJetSource D T S C K V γ t s j v) j.val := by
  obtain ⟨B, hB, hjets⟩ :=
    n05CanonicalSourceLift_allAngularJets h hcoordinates hD hT hγw hgap t M hV
  obtain ⟨A, hA, haux⟩ :=
    n05CanonicalAuxiliaryScalar_volume_bound h hcoordinates hD hT hV hγw hgap t M
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  let ψ : ℕ → PolarPoint → ℝ := fun j =>
    mixedDerivative 0 j ((S.height (3 / 4 : ℝ)).decode S.psi)
  have hψ (j : ℕ) : SourceDerivativeMember D γw M (ψ j) :=
    n05_physicalNormalizer_angular_sourceDerivativeMember hD hS γw M j
  let Q (j : ℕ) : ℝ := sourceNormSquare D γw M (ψ j, 0)
  have hQ (j : ℕ) : 0 ≤ Q j := by
    change 0 ≤ 0 ^ 2 + ∑' m, sourceCellSquare D γw M (ψ j) m
    exact add_nonneg (sq_nonneg _) (tsum_nonneg
      (fun m => sourceCellSquare_nonneg hab γw M (hψ j).1 m))
  let Z : ℝ := ∑ j : Fin (s + 1), Q j.val
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun (j : Fin (s + 1)) _ => hQ j.val)
  have hQZ (j : Fin (s + 1)) : Q j.val ≤ Z :=
    Finset.single_le_sum (fun (k : Fin (s + 1)) _ => hQ k.val) (Finset.mem_univ j)
  refine ⟨2 * (B + A * Z), by positivity, fun v j => ?_⟩
  have hj := hjets s v j
  have hc := n05_sourceDerivativeMember_sub_const_mul_bound hab hj.1 (hψ j.val)
    (n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v))
  have hu : MemLp (n05CanonicalSourceLift S C K (V.forget γ t s v)) 2
      (radialPhysicalMeasure D) :=
    MemLp.ae_eq (n05CanonicalJetSource_zero_ae h hcoordinates hV γ t s v)
      (r11b_sourceDerivative_memLp hD hγw (hjets s v 0).1)
  refine ⟨hc.1, ?_, n05_normalizedSource_weak_angularJet hab hS hu
    (r11b_sourceDerivative_memLp hD hγw hj.1) hj.2.2
      (n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v))⟩
  have hprod : n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v) ^ 2 * Q j.val ≤
      (A * ‖v‖ ^ 2) * Z :=
    mul_le_mul (haux s v) (hQZ j) (hQ j.val) (mul_nonneg hA.le (sq_nonneg _))
  calc
    _ ≤ 2 * (sourceNormSquare D γw M (n05CanonicalJetSource T S C K γ t s j v.val, 0) +
        n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v) ^ 2 * Q j.val) := hc.2
    _ ≤ 2 * (B * ‖v‖ ^ 2 + (A * ‖v‖ ^ 2) * Z) :=
      mul_le_mul_of_nonneg_left (add_le_add hj.2.1 hprod) (by norm_num)
    _ = (2 * (B + A * Z)) * ‖v‖ ^ 2 := by ring

end ContinuousFlexibility.Statements
