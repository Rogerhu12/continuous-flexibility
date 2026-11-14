module

public import ContinuousFlexibility.Analysis.N07aSampleLinearJets

/-!
# Low-source scalar coefficients multiplying actual finite-piece columns

Finite physical support supplies arbitrary material weights without a
height loss. Only a scalar low-source estimate is needed; no linearity
or differentiability in the source parameter is asserted or used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {d low : ℕ}

theorem n07a_finiteCoefficient_weighted_jets
    (hp : Monotone p) {f : E → ℕ → PolarPoint → ℝ}
    (hf : N07aSampleJetBounds T K p U (canonicalOpen S K) d f)
    (I : Finset ℕ)
    (hzero : ∀ z ∈ U, ∀ m, m ∉ I → EqOn (f z m) (fun _ => (0 : ℝ))
      (canonicalOpen S K m))
    (w : ℕ → ℕ → ℝ) (hw : ∀ c m, 0 < w c m) (a b c : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ U, ∀ m y, y ∈ canonicalOpen S K m →
      |mixedDerivative a b (f z m) y| ≤
        C * w c m * (1 + p (c + (a + b) + d) z) := by
  classical
  obtain ⟨e, _, he0, heb⟩ := hf a b
  let C : ℝ := 1 + ∑ m ∈ I, e m / w c m
  have hsum0 : 0 ≤ ∑ m ∈ I, e m / w c m :=
    Finset.sum_nonneg fun m _ => div_nonneg (he0 m) (hw c m).le
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, fun z hz m y hy => ?_⟩
  by_cases hm : m ∈ I
  · have heC : e m / w c m ≤ C :=
      (Finset.single_le_sum (fun n _ => div_nonneg (he0 n) (hw c n).le) hm).trans
        (le_add_of_nonneg_left zero_le_one)
    have hew : e m ≤ C * w c m := (div_le_iff₀ (hw c m)).mp heC
    have hparam : 1 + p (a + b + d) z ≤ 1 + p (c + (a + b) + d) z :=
      add_le_add le_rfl (hp (by omega) z)
    exact (heb z hz m y hy).trans
      (mul_le_mul hew hparam (by positivity) (mul_nonneg hC.le (hw c m).le))
  · have hd := n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ)
      (hzero z hz m hm) a b hy
    have hz' : mixedDerivative a b (f z m) y = 0 := by
      simpa only [mixedDerivative, iteratedDeriv_fun_const_zero] using hd
    rw [hz', abs_zero]
    exact mul_nonneg (mul_nonneg hC.le (hw c m).le)
      (add_nonneg zero_le_one (apply_nonneg _ _))

theorem n07a_finiteScalarColumns_sampleLinearJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hp : Monotone p) (w : ℕ → ℕ → ℝ) (hw : ∀ c m, 0 < w c m)
    (φ : Fin 3 → E → ℕ → PolarPoint → ℝ)
    (hφ : ∀ i, N07aSampleJetBounds T K p U (canonicalOpen S K) d (φ i))
    (hφs : ∀ i z, z ∈ U → ∀ m, ContDiffOn ℝ ∞ (φ i z m) (canonicalOpen S K m))
    (I : Finset ℕ)
    (hzero : ∀ i z, z ∈ U → ∀ m, m ∉ I →
      EqOn (φ i z m) (fun _ => (0 : ℝ)) (canonicalOpen S K m))
    (α : E → F → Fin 3 → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hα : ∀ z ∈ U, ∀ f i, |α z f i| ≤ A * q low f) :
    N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w low d
      (fun z f m y => ∑ i : Fin 3, α z f i * φ i z m y) := by
  classical
  intro a b c
  choose C hC hCb using fun i : Fin 3 =>
    n07a_finiteCoefficient_weighted_jets hp (hφ i) I (hzero i) w hw a b c
  let e : ℝ := A * ∑ i : Fin 3, C i
  have he : 0 ≤ e := mul_nonneg hA (Finset.sum_nonneg fun i _ => (hC i).le)
  refine ⟨fun _ => e, N07aSampleSubpower.const hD hT e, fun _ => he, ?_⟩
  intro z hz f m y hy
  rw [n07a_mixedDerivative_sum_on (isOpen_Ioo.prod isOpen_univ)
    (fun i _ => contDiffOn_const.mul (hφs i z hz m)) a b hy]
  simp_rw [spaces_mixedDerivative_const_mul]
  calc
    |∑ i : Fin 3, α z f i * mixedDerivative a b (φ i z m) y| ≤
        ∑ i : Fin 3, |α z f i| * |mixedDerivative a b (φ i z m) y| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun i : Fin 3 => α z f i * mixedDerivative a b (φ i z m) y) Finset.univ
    _ ≤ ∑ i : Fin 3, (A * q low f) *
        (C i * w c m * (1 + p (c + (a + b) + d) z)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hα z hz f i) (hCb i z hz m y hy) (abs_nonneg _)
        (mul_nonneg hA (apply_nonneg _ _))
    _ = e * w c m * ((1 + p (c + (a + b) + d) z) * q low f) := by
      dsimp only [e]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ e * w c m * (q (c + (a + b) + d) f +
        (1 + p (c + (a + b) + d) z) * q low f) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (apply_nonneg _ _))
        (mul_nonneg he (hw c m).le)

end ContinuousFlexibility.Analysis
