import ContinuousFlexibility.Analysis.N04SourceColumnsData
import ContinuousFlexibility.Analysis.N04SourceColumnsPrefix

/-!
# The selected-piece input towers for negative inversion

The inverse-chart argument works only on negative pieces. Recovering
the full current tower from its reference difference must therefore
retain that predicate, including its proof argument. The reference
enters only at parameter order zero; every positive parameter order
keeps the sampled height gain of the original current data.

All estimates below concern the actual spatial derivatives. A caller
may use any genuine tower of those derivatives, by uniqueness.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Add the fixed reference jet back on each selected piece. -/
def CurrentJetDataOn.negativeInverse_mixedRegularity
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (m : ℕ) (hm : P m) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun z => f z m) where
  spatial z hz := (h.1 z hz m hm).1
  parameter i j q hq :=
    (smoothDirectionsAdd (h.2.choose m hm i j ⟨q, hq⟩)
      (smoothDirections_constant (isOpen_sectorNeighborhood S base ε ε)
        (mixedDerivative i j (f₀ m) q))).congr (fun z hz => by
      rw [mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (h.1 z hz m hm).1 (h₀ m hm) i j hq]
      exact sub_add_cancel _ _)

/-- Any genuine positive-order tower of the current field agrees with
the supplied tower of its reference difference. -/
theorem CurrentJetDataOn.negativeInverse_positive_jet_eq
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip)
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative i j (f z m) q.val))
    {k : ℕ} (hk : 0 < k) {z : Parameter S}
    (hz : z ∈ sectorNeighborhood S base ε ε) (v : Fin k → Parameter S) :
    J.D k z v = (h.2.choose m hm i j q).D k z v := by
  let K := (h.2.choose m hm i j q).congr (fun z hz =>
    mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
      (h.1 z hz m hm).1 (h₀ m hm) i j q.property)
  exact (smoothDirections_D_sub_constant J K hk hz v).symm

/-- The original positive-order estimate controls any genuine current
tower, with the same low order, loss and selected-piece sample. -/
theorem CurrentJetDataOn.negativeInverse_positiveTower
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip) :
    ∀ k : ℕ, 0 < k → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading S) base (s + loss) z v := by
  intro k hk
  have ht := h.2.choose_spec.2 k
  refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
    (ht.choose_spec s).choose_spec.1, ?_⟩⟩
  intro m hm q hq i j hij J z hz v
  rw [h.negativeInverse_positive_jet_eq h₀ m hm i j ⟨q, hq⟩ J hk hz v]
  exact (ht.choose_spec s).choose_spec.2 z hz v m hm ⟨q, hq⟩ i j hij

/-- Including the unweighted reference at order zero gives the full
current tower. Positive parameter orders retain the full height factor. -/
theorem CurrentJetDataOn.negativeInverse_fullTower
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, P m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (f₀ m) q| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
            oneHighVariationWeight (parameterGrading S) base (s + loss) z v := by
  intro k
  by_cases hk : k = 0
  · subst k
    have hheight := material_sample_height_coefficient_power_bounded hD hT cell 0
      (by norm_num : (0 : ℝ) < 3 / 4)
    let CH : ℝ := hheight.choose
    have hCH : 0 < CH := hheight.choose_spec.1
    have hheight' (m : ℕ) : T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ CH := by
      simpa only [CH, Real.rpow_zero, mul_one] using hheight.choose_spec.2 m
    have hv := h.2.choose_spec.1
    refine ⟨hv.choose, fun s => ?_⟩
    have hd := hv.choose_spec s
    have hr := href s
    have hc := n04Realization_referenceAndDifferenceEnvelope hr.choose_spec.1.le
      hd.choose_spec.1.le hCH.le
    refine ⟨hc.choose, hc.choose_spec.1, ?_⟩
    intro m hm q hq i j hij J z hz v
    have he : mixedDerivative i j (f z m) q =
        mixedDerivative i j (fun y => f z m y - f₀ m y) q +
          mixedDerivative i j (f₀ m) q := by
      rw [mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (h.1 z hz m hm).1 (h₀ m hm) i j hq]
      exact (sub_add_cancel _ _).symm
    have hb := hc.choose_spec.2 (T.E0 (T.sample (cell m)))
      (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
      (parameterGrading S (s + hv.choose) z) _ _ (hE m) (hheight' m) (apply_nonneg _ _)
      (hr.choose_spec.2 m hm q hq i j hij)
      (hd.choose_spec.2 z hz m hm ⟨q, hq⟩ i j hij)
    simpa only [smoothDirections_D_zero_apply J hz v, parameterHeightWeight,
      ite_true, mul_one, oneHighVariationWeight, Finset.univ_eq_empty,
      Finset.prod_empty, Finset.sum_empty, add_zero] using (congrArg abs he).trans_le hb
  · have ht := h.negativeInverse_positiveTower h₀ k (Nat.pos_of_ne_zero hk)
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro m hm q hq i j hij J z hz v
    simpa only [parameterHeightWeight, if_neg hk] using
      (ht.choose_spec s).choose_spec.2 m hm q hq i j hij J z hz v

/-- Selected current data admit raw interpolation bounds with one low
order before the parameter prefix. The finite shift may depend on that
prefix; the low order and the height exponent do not. -/
theorem CurrentJetDataOn.negativeInverse_prefix_power
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, P m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (f₀ m) q| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    ∃ b : ℕ, base ≤ b ∧ ∀ K : ℕ, ∃ shift : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ k, k ≤ K → ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j,
      i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S b z ≤ 1 →
      ∀ v : Fin k → Parameter S, (∀ l, parameterGrading S b (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading S (b + s + shift * K + 1) z ≤ R →
        (∀ l, parameterGrading S (b + s + shift * K + 1) (v l) ≤ R) →
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
            R ^ (((i + j + shift * k : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  let I : Type := {m : ℕ // P m}
  let RF (m : I) := h.negativeInverse_mixedRegularity h₀ m.val m.property
  have ht := h.negativeInverse_fullTower hD hT h₀ href hE
  let L : ℕ → ℕ := fun k => (ht k).choose
  have hb (k s : ℕ) : ∃ B : ℝ, 0 < B ∧
      ∀ m : I, ∀ q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |((RF m).parameter i j q hq).D k z v| ≤
          B * T.E0 (T.sample (cell m.val)) ^ B *
            parameterHeightWeight (T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) k *
              oneHighVariationWeight (parameterGrading S) base (s + L k) z v := by
    have hs := (ht k).choose_spec s
    exact ⟨hs.choose, hs.choose_spec.1,
      fun m q hq i j hij z hz v => hs.choose_spec.2 m.val m.property q hq i j hij
        ((RF m).parameter i j q hq) z hz v⟩
  obtain ⟨b, hbase, hprefix⟩ := n04SourceColumns_prefix_power (parameterGrading S)
    (tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl))
    hI base L (fun m : I => T.E0 (T.sample (cell m.val)))
    (fun k m => parameterHeightWeight (T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) k)
    (fun m => hE m.val)
    (fun k m => parameterHeightWeight_nonneg (Real.rpow_nonneg (hH m.val) _) k)
    (fun m z => f z m.val) RF hb
  refine ⟨b, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hshift s
  refine ⟨B, hB, ?_⟩
  intro k hk m hm q hq i j hij J z hz hlow v hv R hR hzR hvR
  have he := congrArg (fun A : (Parameter S) [×k]→L[ℝ] ℝ => A v)
    (J.unique ((RF ⟨m, hm⟩).parameter i j q hq) k z hz)
  rw [he]
  exact hbound k hk ⟨m, hm⟩ q hq i j hij z hz hlow v hv R hR hzR hvR

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_fullTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_fullTower

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_prefix_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_prefix_power
