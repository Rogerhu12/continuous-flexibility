module

public import ContinuousFlexibility.Analysis.N04NegativeInverseCollector
public import ContinuousFlexibility.Analysis.N04NegativeInverseMixedPrefix

/-!
# Genuine joint prefixes and their mixed derivative bounds

Only the original positive parameter arity is fixed. Appending spatial
directions preserves that arity and its sampled height factor. The
conversion is proved independently of any concrete realization gauge.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- Convert one finite prefix with abstract seminorms and scalar weights,
before supplying the concrete sector grading. -/
private theorem negativeInverse_fractionalMixed_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : Set PolarPoint} {f : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (low high : Seminorm ℝ E) (k a b s shift : ℕ)
    (hk : 0 < k) (hab : a + b ≤ s)
    (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    {M H R : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hR : 1 ≤ R)
    (hraw : ∀ n : ℕ, 0 < n → n ≤ k + a + b →
      ∀ w : StateAngleWord n, w.stateArity = k → w.angleArity ≤ s →
      ∀ u : Fin n → E × PolarPoint,
      (∀ i, low (u i).1 ≤ 1) → (∀ i, high (u i).1 ≤ R) →
      (∀ i, ‖(u i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (u i).1 = 0) →
      (∀ i, w.isState i = true → (u i).2 = 0) →
        ‖J.D n (x, q) u‖ ≤ M * H *
          R ^ (((w.angleArity + shift * k - 1 : ℕ) : ℝ) /
            (((s + shift * k : ℕ) : ℝ) + 1)))
    (Q : SmoothDirections U (fun z => mixedDerivative a b (fun p => f (z, p)) q))
    (v : Fin k → E) (hlow : ∀ i, low (v i) ≤ 1)
    (hhigh : ∀ i, high (v i) ≤ R) :
    |Q.D k x v| ≤ M * H *
      R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
  let t : ℝ := R ^ (1 / (((s + shift * k : ℕ) : ℝ) + 1))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hp (d : ℕ) : t ^ d = R ^ ((d : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) :=
    n04NegativeInverse_commonScale_pow (zero_le_one.trans hR) d (s + shift * k)
  have h := n04NegativeInverse_mixed_of_pureJoint J hU hV hc low high
    (zero_le_one.trans hR) hM hH ht k a b shift hk x hx q hq
    (fun n hn hns w hw u hu huh hup hus hsp => by
      have hs : w.angleArity ≤ s := by have hsum := w.arity_sum; omega
      have hbound := hraw n hn hns w hw hs u hu huh hup hus hsp
      rw [parameterHeightWeight, if_neg (Nat.ne_of_gt hk), hp]
      simpa only [Real.norm_eq_abs] using hbound)
    Q v hlow hhigh
  rw [parameterHeightWeight, if_neg (Nat.ne_of_gt hk), hp] at h
  exact h

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
  let orderData := hraw k hk
  let shift : ℕ := orderData.choose
  have hshift := orderData.choose_spec
  refine ⟨shift, fun s => ?_⟩
  let boundData := hshift s
  let B : ℝ := boundData.choose
  have hB : 0 < B := boundData.choose_spec.1
  have hb := boundData.choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro m hm q hq a b hab Q z hz v hv R hR hzR hvR
  have hM : 0 ≤ B * T.E0 (T.sample (cell m)) ^ B :=
    mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)
  have hheight : 0 ≤ T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hH m) _
  exact negativeInverse_fractionalMixed_bound (J m hm)
    (sectorNeighborhood_isOpen S base ε ε) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))
    (parameterGrading S base) (parameterGrading S (base + s + shift * k + 1))
    k a b s shift hk hab z hz q hq hM hheight hR
    (fun n _ _ w hw hs u hu huh hup hus hsp =>
      hb m hm (J m hm) z hz q hq n w hw hs u hu R hR hzR huh hup hus hsp)
    Q v hv hvR

end ContinuousFlexibility.Analysis
