import ContinuousFlexibility.Analysis.N04NegativeInverseCollector
import ContinuousFlexibility.Analysis.N04NegativeInverseOutputAtoms
import ContinuousFlexibility.Analysis.N04NegativeInverseReferenceBounds

/-!
# Collect genuine point and height joint estimates

The quantitative geometry argument has two outputs: the actual inverse
point and the actual pulled height. This file turns their positive
joint prefixes into all three current-data fields on the same fixed
neighborhood. Fixed physical normalization costs are absorbed only in
the polynomial E0 coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

/-- Only the original positive parameter arity is fixed. The spatial
arity may vary up to the requested order on the same finite prefix. -/
def N04NegativeInverseJointPrefixes
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : PhysicalSpacesData) (T : MaterialData) (cell : ℕ → ℕ)
    (P : ℕ → Prop) (base : ℕ) (ε : ℝ)
    (f : Parameter S → ℕ → PolarPoint → F) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ shift : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m, P m →
    ∀ J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
      (fun x : Parameter S × PolarPoint => f x.1 m x.2),
    ∀ z ∈ sectorNeighborhood S base ε ε, ∀ q ∈ unitStrip,
    ∀ n : ℕ, ∀ w : StateAngleWord n, w.stateArity = k → w.angleArity ≤ s →
    ∀ v : Fin n → Parameter S × PolarPoint,
    (∀ i, parameterGrading S base (v i).1 ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → parameterGrading S (base + s + shift * k + 1) z ≤ R →
      (∀ i, parameterGrading S (base + s + shift * k + 1) (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
      ‖J.D n (z, q) v‖ ≤ B * T.E0 (T.sample (cell m)) ^ B *
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
          R ^ (((w.angleArity + shift * k - 1 : ℕ) : ℝ) /
            (((s + shift * k : ℕ) : ℝ) + 1))

theorem n04NegativeInverse_rawPrefixes_of_joint
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ}
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (J : ∀ m, P m → SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
      (fun x : Parameter S × PolarPoint => f x.1 m x.2))
    (hraw : N04NegativeInverseJointPrefixes S T cell P base ε f) :
    N04NegativeInverseRawPrefixes S T cell P base ε f := by
  intro k hk
  obtain ⟨shift, hshift⟩ := hraw k hk
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hshift s
  refine ⟨B, hB, ?_⟩
  intro m hm q hq a b hab Q z hz v hv R hR hzR hvR
  let t : ℝ := R ^ (1 / (((s + shift * k : ℕ) : ℝ) + 1))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hp (d : ℕ) : t ^ d = R ^ ((d : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) :=
    n04NegativeInverse_commonScale_pow (zero_le_one.trans hR) d (s + shift * k)
  have hM : 0 ≤ B * T.E0 (T.sample (cell m)) ^ B :=
    mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)
  have hheight : 0 ≤ T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hH m) _
  have h := n04NegativeInverse_mixed_of_pureJoint (J m hm)
    (sectorNeighborhood_isOpen S base ε ε) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))
    (parameterGrading S base) (parameterGrading S (base + s + shift * k + 1))
    (zero_le_one.trans hR) hM hheight ht k a b shift hk z hz q hq
    (fun n hn hns w hw u hu huh hup hus hsp => by
      have hs : w.angleArity ≤ s := by have hsum := w.arity_sum; omega
      have hbound := hb m hm (J m hm) z hz q hq n w hw hs u hu R hR hzR huh hup hus hsp
      rw [parameterHeightWeight, if_neg (Nat.ne_of_gt hk), hp]
      simpa only [Real.norm_eq_abs] using hbound)
    Q v hv hvR
  rw [parameterHeightWeight, if_neg (Nat.ne_of_gt hk), hp] at h
  exact h

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem negativeInverse_atom_jointPrefixes
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (hpoint : N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (fun z m q => G.pulledPoint 0 (G.lift 0 z) m q))
    (a : Atom) (ha : atomIsNegativeInverse a) :
    N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (G.atomFamily 0 a) := by
  obtain ⟨C, hC, hc⟩ := G.negativeInverse_length_values
  intro k hk
  obtain ⟨shift, hshift⟩ := hpoint k hk
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hshift s
  obtain ⟨D, hD, hpack⟩ := coefficientEnvelope_pack ((1 + C) * B) (C + B)
  refine ⟨D, hD, ?_⟩
  intro m hm J z hz q hq n w hw hs v hv R hR hzR hvR hp hstate hspatial
  let P := (G.negativeInversePointJointTower 0 m hm).restrict
    ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩)
  have hP := hb m hm P z hz q hq n w hw hs v hv R hR hzR hvR hp hstate hspatial
  have hA := G.negativeInverseAtom_positiveJoint_bound 0 m P a ha J w
    (hw.symm ▸ hk) ⟨hz, hq⟩ v hspatial
  let E : ℝ := G.W.U.E0 (G.W.U.sample ((G.V 0).cell m))
  let H : ℝ := G.W.U.H (G.W.U.sample ((G.V 0).cell m)) ^ (3 / 4 : ℝ)
  let W : ℝ := R ^ (((w.angleArity + shift * k - 1 : ℕ) : ℝ) /
    (((s + shift * k : ℕ) : ℝ) + 1))
  have hE : 1 ≤ E := (G.cost_nonneg 0).2.2 m
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg 0).2.1 m) _
  have hW : 0 ≤ W := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hinv : |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹| ≤ C * E ^ C := by
    rw [abs_of_pos (inv_pos.mpr (hc 0 m).1)]
    exact (hc 0 m).2.2.2.1
  have hcoef : (1 + |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹|) *
      (B * E ^ B) ≤ D * E ^ D := by
    have hCp : 1 ≤ E ^ C := Real.one_le_rpow hE hC.le
    calc
      _ ≤ ((1 + C) * E ^ C) * (B * E ^ B) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hinv])
          (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans hE) _))
      _ = ((1 + C) * B) * E ^ (C + B) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hE)]
        ring
      _ ≤ _ := hpack E hE
  have hraw : |J.D n (z, q) v| ≤ D * E ^ D * H * W := by
    calc
      _ ≤ (1 + |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹|) * ‖P.D n (z, q) v‖ := hA
      _ ≤ (1 + |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹|) *
          (B * E ^ B * H * W) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
      _ = ((1 + |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹|) *
          (B * E ^ B)) * H * W := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef hH) hW
  simpa only [Real.norm_eq_abs] using hraw

/-- The point and pulled-height joint estimates close exactly the
inverse subnode's conclusion on the supplied common neighborhood. -/
theorem negativeInverse_collect_joint
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε) (hsmall : ε ≤ 1 / 2)
    (hpoint : N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (fun z m q => G.pulledPoint 0 (G.lift 0 z) m q))
    (hheight : N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (G.pulledHeight 0)) :
    ∀ η, G.NegativeAtomData η atomIsNegativeInverse b ε ∧
      G.Data η (G.Neg η) b ε (G.pulledHeight η) (G.pulledHeightRef η) := by
  apply G.negativeInverse_collect hadm hsmall
  · intro a ha
    apply n04NegativeInverse_rawPrefixes_of_joint
      (S := G.S 0) (T := G.W.U) (cell := (G.V 0).cell) (P := G.Neg 0)
      (base := b) (ε := ε) (f := G.atomFamily 0 a)
      (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
      (fun m hm => (G.negativeInverseAtomJointTower 0 m hm a ha).restrict
        ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
        (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩))
    exact G.negativeInverse_atom_jointPrefixes hadm hpoint a ha
  · apply n04NegativeInverse_rawPrefixes_of_joint
      (S := G.S 0) (T := G.W.U) (cell := (G.V 0).cell) (P := G.Neg 0)
      (base := b) (ε := ε) (f := G.pulledHeight 0)
      (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
      (fun m hm => (G.negativePulledHeightJointTower 0 m hm).restrict
        ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
        (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩))
    exact hheight

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_collect_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_collect_joint
