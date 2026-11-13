import ContinuousFlexibility.Analysis.N04NegativeInverseCurrentTowers
import ContinuousFlexibility.Analysis.N04NegativeInversePrefixPower

/-!
# One low base for a finite family of actual negative atoms

Finite sums dominate the individual order losses and material envelopes.
The scalar prefix theorem is then applied once to the product of the atom
index and the selected component index. Its low base precedes the prefix,
and its shift precedes the spatial order, uniformly in both indices.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

private theorem n04NegativeInverse_finiteFamily_raw
    {X A I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [Fintype A]
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base : ℕ)
    {U : Set X} {Ω : Set PolarPoint}
    (E : I → ℝ) (W : ℕ → I → ℝ)
    (hE : ∀ t, 1 ≤ E t) (hW : ∀ k t, 0 ≤ W k t)
    {f : A × I → X → PolarPoint → ℝ}
    (RF : ∀ t, MixedJetRegularity U Ω (f t))
    (hbound : ∀ a : A, ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ t q (hq : q ∈ Ω) i j, i + j ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF (a, t)).parameter i j q hq).D k x v| ≤
          B * E t ^ B * W k t * oneHighVariationWeight p base (s + loss) x v) :
    ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ t : A × I, ∀ q (hq : q ∈ Ω) i j, i + j ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF t).parameter i j q hq).D k x v| ≤
          B * E t.2 ^ B * W k t.2 * oneHighVariationWeight p base (s + loss) x v := by
  classical
  intro k
  choose L hL using fun a => hbound a k
  let loss : ℕ := ∑ a : A, L a
  have hLoss (a : A) : L a ≤ loss :=
    Finset.single_le_sum (fun b _ => Nat.zero_le (L b)) (Finset.mem_univ a)
  refine ⟨loss, fun s => ?_⟩
  choose c hc hb using fun a => hL a s
  let B : ℝ := 1 + ∑ a : A, c a
  have hsum : 0 ≤ ∑ a : A, c a := Finset.sum_nonneg (fun a _ => (hc a).le)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hcB (a : A) : c a ≤ B :=
    (Finset.single_le_sum (fun b _ => (hc b).le) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨B, hB, ?_⟩
  intro t q hq i j hij x hx v
  have hcoef : c t.1 * E t.2 ^ c t.1 ≤ B * E t.2 ^ B :=
    mul_le_mul (hcB t.1) (Real.rpow_le_rpow_of_exponent_le (hE t.2) (hcB t.1))
      (Real.rpow_nonneg (zero_le_one.trans (hE t.2)) _) hB.le
  have hweight : oneHighVariationWeight p base (s + L t.1) x v ≤
      oneHighVariationWeight p base (s + loss) x v :=
    oneHighVariationWeight_mono hp le_rfl (Nat.add_le_add_left (hLoss t.1) s) x v
  have hnonneg : 0 ≤ B * E t.2 ^ B * W k t.2 :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE t.2)) _))
      (hW k t.2)
  exact (hb t.1 t.2 q hq i j hij x hx v).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (hW k t.2))
      (oneHighVariationWeight_nonneg p base (s + L t.1) x v)).trans
      (mul_le_mul_of_nonneg_left hweight hnonneg))

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

/-- A finite family shares one low base before every parameter prefix and
one shift before every spatial order. Every bound is uniform in the atom
and selected component, with the exact inverse degree `i + j + shift * k - 1`. -/
theorem CurrentJetDataOn.negativeInverse_finiteFamily_sharpPrefix_power
    {A : Type*} [Fintype A]
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : A → Parameter S → ℕ → PolarPoint → ℝ}
    {f₀ : A → ℕ → PolarPoint → ℝ}
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (h : ∀ a, CurrentJetDataOn S T cell P base ε (f a) (f₀ a))
    (h₀ : ∀ a m, P m → ContDiffOn ℝ ∞ (f₀ a m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ a m, P m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (f₀ a m) q| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    ∃ b : ℕ, base ≤ b ∧ ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧ ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ a k, k ≤ K →
      ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f a z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S b z ≤ 1 →
      ∀ v : Fin k → Parameter S, (∀ l, parameterGrading S b (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading S (b + s + shift * K + 1) z ≤ R →
        (∀ l, parameterGrading S (b + s + shift * K + 1) (v l) ≤ R) →
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
            R ^ (((i + j + shift * k - 1 : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  let I : Type := {m : ℕ // P m}
  let RF (t : A × I) : MixedJetRegularity
      (sectorNeighborhood S base ε ε) unitStrip (fun z => f t.1 z t.2.val) :=
    (h t.1).negativeInverse_mixedRegularity (h₀ t.1) t.2.val t.2.property
  have hp : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  have hrefa (a : A) (s : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ m, P m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (f₀ a m) q| ≤ B * T.E0 (T.sample (cell m)) ^ B := by
    obtain ⟨B, hB, hb⟩ := href s
    exact ⟨B, hB, fun m hm q hq i j hij => hb a m hm q hq i j hij⟩
  have ht := n04NegativeInverse_finiteFamily_raw (parameterGrading S) hp base
    (fun m : I => T.E0 (T.sample (cell m.val)))
    (fun (k : ℕ) (m : I) =>
      parameterHeightWeight (T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) k)
    (fun m => hE m.val)
    (fun k m => parameterHeightWeight_nonneg (Real.rpow_nonneg (hH m.val) _) k) RF
    (fun a k => by
      obtain ⟨L, hL⟩ := (h a).negativeInverse_fullTower hD hT (h₀ a) (hrefa a) hE k
      refine ⟨L, fun s => ?_⟩
      obtain ⟨B, hB, hb⟩ := hL s
      exact ⟨B, hB, fun m q hq i j hij z hz v =>
        hb m.val m.property q hq i j hij ((RF (a, m)).parameter i j q hq) z hz v⟩)
  let L : ℕ → ℕ := fun k => (ht k).choose
  have hb (k s : ℕ) := (ht k).choose_spec s
  obtain ⟨b, hbase, hprefix⟩ := n04NegativeInverse_scalar_prefix_power
    (parameterGrading S) hp hI base L
    (fun t : A × I => T.E0 (T.sample (cell t.2.val)))
    (fun k t => parameterHeightWeight (T.H (T.sample (cell t.2.val)) ^ (3 / 4 : ℝ)) k)
    (fun t => hE t.2.val)
    (fun k t => parameterHeightWeight_nonneg (Real.rpow_nonneg (hH t.2.val) _) k)
    (fun t z => f t.1 z t.2.val) RF hb
  refine ⟨b, hbase, fun K => ?_⟩
  obtain ⟨shift, hshiftOne, hshift⟩ := hprefix K
  refine ⟨shift, hshiftOne, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hshift s
  refine ⟨B, hB, ?_⟩
  intro a k hk m hm q hq i j hij J z hz hlow v hv R hR hzR hvR
  have he := congrArg (fun M : (Parameter S) [×k]→L[ℝ] ℝ => M v)
    (J.unique ((RF (a, ⟨m, hm⟩)).parameter i j q hq) k z hz)
  rw [he]
  exact hbound k hk (a, ⟨m, hm⟩) q hq i j hij z hz hlow v hv R hR hzR hvR

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_finiteFamily_sharpPrefix_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_finiteFamily_sharpPrefix_power
