import ContinuousFlexibility.Analysis.N07aSampleFrechetBounds
import ContinuousFlexibility.Analysis.OneHighCompositionJets

/-!
# Actual spatial jets at a fixed admissible parameter

This finite-calculus interface keeps the sampled height factor outside
every coefficient envelope. It is used only for membership in the genuine
reference graph; the uniform one-high estimates are supplied separately.
No inverse or regularity conclusion is a premise of the construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff BigOperators Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

def N07aAngularFixedJetEnvelope
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : MaterialData) {S : PhysicalSpacesData} (K : CanonicalData S)
    (W : ℕ → Set E) (w : ℕ → ℝ) (f : ℕ → E → F) : Prop :=
  ∀ n : ℕ, ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
    ∀ m x, x ∈ W m → ‖iteratedFDeriv ℝ n (f m) x‖ ≤ e m * w m

namespace N07aAngularFixedJetEnvelope

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem congr {W : ℕ → Set E} {w : ℕ → ℝ} {f g : ℕ → E → F}
    (hf : N07aAngularFixedJetEnvelope T K W w f)
    (hW : ∀ m, IsOpen (W m)) (he : ∀ m, EqOn (g m) (f m) (W m)) :
    N07aAngularFixedJetEnvelope T K W w g := by
  intro n
  obtain ⟨e, hsub, he0, hb⟩ := hf n
  refine ⟨e, hsub, he0, fun m x hx => ?_⟩
  have hloc : g m =ᶠ[𝓝 x] f m := by
    filter_upwards [(hW m).mem_nhds hx] with y hy
    exact he m hy
  rw [(hloc.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hb m x hx

theorem comp
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set E} {V : ℕ → Set F} {w : ℕ → ℝ}
    {f : ℕ → F → G} {Φ : ℕ → E → F}
    (hf : N07aAngularFixedJetEnvelope T K V w f) (hw : ∀ m, 0 ≤ w m)
    (hmaps : ∀ m, MapsTo (Φ m) (W m) (V m))
    (hfs : ∀ m x, x ∈ W m → ContDiffAt ℝ ∞ (f m) (Φ m x))
    (hΦs : ∀ m x, x ∈ W m → ContDiffAt ℝ ∞ (Φ m) x)
    (hΦ : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ m x, x ∈ W m → ‖iteratedFDeriv ℝ n (Φ m) x‖ ≤ e m) :
    N07aAngularFixedJetEnvelope T K W w (fun m => f m ∘ Φ m) := by
  classical
  intro n
  choose a ha ha0 hab using fun k : OrderedFinpartition n => hf k.length
  choose b hb hb0 hbb using fun k : OrderedFinpartition n =>
    fun j : Fin k.length => hΦ (k.partSize j) (k.partSize_pos j)
  let e : OrderedFinpartition n → ℕ → ℝ := fun k m => a k m * ∏ j, b k j m
  have he (k : OrderedFinpartition n) : N07aSampleSubpower T K (e k) :=
    N07aSampleSubpower.mul hD hT (ha k)
      (N07aSampleSubpower.finset_prod hD hT Finset.univ (b k) (fun j _ => hb k j))
  refine ⟨fun m => ∑ k, e k m,
    N07aSampleSubpower.finset_sum hD hT Finset.univ e (fun k _ => he k),
    fun m => Finset.sum_nonneg (fun k _ =>
      mul_nonneg (ha0 k m) (Finset.prod_nonneg (fun j _ => hb0 k j m))), ?_⟩
  intro m x hx
  apply (norm_iteratedFDeriv_comp_le_partition_sum (hfs m x hx) (hΦs m x hx) n).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  have hprod : (∏ j, ‖iteratedFDeriv ℝ (k.partSize j) (Φ m) x‖) ≤ ∏ j, b k j m :=
    Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hbb k j m x hx)
  exact (mul_le_mul (hab k m (Φ m x) (hmaps m hx)) hprod
    (Finset.prod_nonneg (fun j _ => norm_nonneg _))
    (mul_nonneg (ha0 k m) (hw m))).trans_eq (by dsimp only [e]; ring)

theorem mul
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set E} {v w : ℕ → ℝ} {f g : ℕ → E → ℝ}
    (hW : ∀ m, IsOpen (W m))
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (W m))
    (hgs : ∀ m, ContDiffOn ℝ ∞ (g m) (W m))
    (hf : N07aAngularFixedJetEnvelope T K W v f)
    (hg : N07aAngularFixedJetEnvelope T K W w g)
    (hv : ∀ m, 0 ≤ v m) (hw : ∀ m, 0 ≤ w m) :
    N07aAngularFixedJetEnvelope T K W (fun m => v m * w m)
      (fun m x => f m x * g m x) := by
  classical
  intro n
  choose a ha ha0 hab using fun i : ℕ => hf i
  choose b hb hb0 hbb using fun i : ℕ => hg (n - i)
  let e : ℕ → ℕ → ℝ := fun i m => (n.choose i : ℝ) * a i m * b i m
  have he (i : ℕ) : N07aSampleSubpower T K (e i) :=
    N07aSampleSubpower.mul hD hT
      (N07aSampleSubpower.mul hD hT
        (N07aSampleSubpower.const hD hT (n.choose i : ℝ)) (ha i)) (hb i)
  refine ⟨fun m => ∑ i ∈ Finset.range (n + 1), e i m,
    N07aSampleSubpower.finset_sum hD hT (Finset.range (n + 1)) e (fun i _ => he i),
    fun m => Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha0 i m)) (hb0 i m)), ?_⟩
  intro m x hx
  have hleibniz := norm_iteratedFDerivWithin_mul_le (hfs m) (hgs m)
    (hW m).uniqueDiffOn hx (by simp : (n : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ (hW m) hx] at hleibniz
  apply hleibniz.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hbound := mul_le_mul
    (mul_le_mul_of_nonneg_left (hab i m x hx) (Nat.cast_nonneg (n.choose i)))
    (hbb i m x hx) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (ha0 i m) (hv m)))
  exact hbound.trans_eq (by dsimp only [e]; ring)

end N07aAngularFixedJetEnvelope

theorem n07a_fixedJetEnvelope_of_sampleJetBounds
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {p : ℕ → Seminorm ℝ E} {U : Set E} {W : ℕ → Set PolarPoint}
    {d : ℕ} {f : E → ℕ → PolarPoint → ℝ}
    (hf : N07aSampleJetBounds T K p U W d f)
    (hW : ∀ m, IsOpen (W m))
    (hfs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (f z m) (W m))
    (z : E) (hz : z ∈ U) :
    N07aAngularFixedJetEnvelope T K W (fun _ => 1) (f z) := by
  intro n
  obtain ⟨e, he, he0, heb⟩ := hf.iteratedFDeriv hD hT hW hfs n
  let c : ℝ := 1 + p (n + d) z
  have hc : 0 ≤ c := add_nonneg zero_le_one (apply_nonneg _ _)
  refine ⟨fun m => e m * c,
    N07aSampleSubpower.mul hD hT he (N07aSampleSubpower.const hD hT c),
    fun m => mul_nonneg (he0 m) hc, fun m x hx => ?_⟩
  simpa only [mul_one] using heb z hz m x hx

end ContinuousFlexibility.Analysis
