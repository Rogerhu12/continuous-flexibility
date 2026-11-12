import ContinuousFlexibility.Analysis.N04RealizationTwoEndpointCubicJets

/-!
# Cubic parameter estimates on an arbitrary fixed component

Translation identifies the existing physical cubic factor with its
zero-based version. It contributes no derivative multiplier. Consequently
the same genuine numerator majorants give the actual divided field's
mixed and parameter jets, with loss six and no neighborhood change.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {l r : ℝ} {N e : E → PolarPoint → ℝ}

/-- The actual open-component factorization produces a genuine divided
mixed tower and transfers every continuous numerator majorant. No bound
for the divided field, and no parameter tower at an endpoint, is assumed. -/
theorem n04Realization_intervalCubic_parameterJets
    (hU : IsOpen U) (hlr : l < r)
    (RN : MixedJetRegularity U (Ioo l r ×ˢ (univ : Set ℝ)) N)
    (hrep : ∀ x ∈ U, ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (N x) (Ioo l r ×ˢ (univ : Set ℝ)) ∧
      ∀ c : Bool, ∀ θ i, i ≤ 2 →
        iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then r else l) = 0)
    (hfactor : ∀ x ∈ U, ∀ q ∈ Ioo l r ×ˢ (univ : Set ℝ),
      N x q = ((q.1 - l) * (r - q.1)) ^ 3 * e x q)
    (G : ∀ k : ℕ, ℕ → ℕ → E × (Fin k → E) → ℝ)
    (hG : ∀ k a b, Continuous (G k a b))
    (hbound : ∀ k a b q (hq : q ∈ Ioo l r ×ˢ (univ : Set ℝ)),
      ∀ x ∈ U, ∀ v : Fin k → E,
        |(RN.parameter a b q hq).D k x v| ≤ G k a b (x, v)) :
    ∃ RE : MixedJetRegularity U (Ioo l r ×ˢ (univ : Set ℝ)) e,
      ∀ k a b p (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ)),
        ∀ x ∈ U, ∀ v : Fin k → E,
          |(RE.parameter a b p hp).D k x v| ≤ G k (a + 6) b (x, v) / 4 := by
  let Ω : Set PolarPoint := Ioo l r ×ˢ (univ : Set ℝ)
  let Ω₀ : Set PolarPoint := Ioo (0 : ℝ) (r - l) ×ˢ (univ : Set ℝ)
  have hmap (q : PolarPoint) (hq : q ∈ Ω₀) : (l + q.1, q.2) ∈ Ω :=
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩
  let N₀ : E → PolarPoint → ℝ := fun x => translateRadialField l (N x)
  let e₀ : E → PolarPoint → ℝ := fun x => translateRadialField l (e x)
  let RN₀ : MixedJetRegularity U Ω₀ N₀ := n04Realization_mixedJetRegularity_translate RN
  have hr₀ : ∀ x ∈ U, ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (N₀ x) Ω₀ ∧ ∀ c : Bool, ∀ θ i, i ≤ 2 →
        iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then r - l else 0) = 0 := by
    intro x hx
    obtain ⟨F, hF, he, hz⟩ := hrep x hx
    refine ⟨translateRadialField l F,
      hF.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd),
      (fun q hq => he _ (hmap q hq)), ?_⟩
    intro c θ i hi
    have hendpoint : l + (if c then r - l else 0) = if c then r else l := by
      cases c <;> simp <;> ring
    calc
      iteratedDeriv i (fun t : ℝ => translateRadialField l F (t, θ))
          (if c then r - l else 0) =
        iteratedDeriv i (fun t : ℝ => F (t, θ)) (l + (if c then r - l else 0)) :=
          congrFun (iteratedDeriv_comp_const_add i (fun t : ℝ => F (t, θ)) l) _
      _ = 0 := by rw [hendpoint]; exact hz c θ i hi
  have hf₀ : ∀ x ∈ U, ∀ q ∈ Ω₀,
      N₀ x q = (q.1 * ((r - l) - q.1)) ^ 3 * e₀ x q := by
    intro x hx q hq
    change N x (l + q.1, q.2) =
      (q.1 * ((r - l) - q.1)) ^ 3 * e x (l + q.1, q.2)
    rw [hfactor x hx _ (hmap q hq)]
    ring
  have hb₀ (k a b : ℕ) (q : PolarPoint) (hq : q ∈ Ω₀)
      (x : E) (hx : x ∈ U) (v : Fin k → E) :
      |(RN₀.parameter a b q hq).D k x v| ≤ G k a b (x, v) := by
    have he := n04Realization_smoothDirections_D_const_mul
      (RN.parameter a b (l + q.1, q.2) (hmap q hq)) (RN₀.parameter a b q hq) 1
      (fun y _ => by simpa only [one_mul] using
        mixedDerivative_translateRadialField l (N y) a b q) k hx v
    rw [he, one_mul]
    exact hbound k a b (l + q.1, q.2) (hmap q hq) x hx v
  obtain ⟨RE₀, hE₀⟩ := n04Realization_twoEndpointCubic_parameterJets
    hU (sub_pos.mpr hlr) RN₀ hr₀ hf₀ G hG hb₀
  let RE : MixedJetRegularity U Ω e :=
    n04Realization_mixedJetRegularity_of_staticFactorization RN hU
      (isOpen_Ioo.prod isOpen_univ)
      (((contDiff_fst.sub contDiff_const).mul
        (contDiff_const.sub contDiff_fst)).pow 3).contDiffOn
      (fun q hq => pow_ne_zero 3
        (mul_pos (sub_pos.mpr hq.1.1) (sub_pos.mpr hq.1.2)).ne') hfactor
  refine ⟨RE, ?_⟩
  intro k a b p hp x hx v
  have hp₀ : (p.1 - l, p.2) ∈ Ω₀ :=
    ⟨⟨sub_pos.mpr hp.1.1, by linarith [hp.1.2]⟩, mem_univ _⟩
  have he := n04Realization_smoothDirections_D_const_mul
    (RE.parameter a b p hp) (RE₀.parameter a b (p.1 - l, p.2) hp₀) 1
    (fun y _ => by
      have hpoint : (l + (p.1 - l), p.2) = p := by
        apply Prod.ext
        · ring
        · rfl
      simpa only [Prod.fst, Prod.snd, hpoint, one_mul] using
        mixedDerivative_translateRadialField l (e y) a b (p.1 - l, p.2)) k hx v
  have hb := hE₀ k a b (p.1 - l, p.2) hp₀ x hx v
  simpa only [he, one_mul] using hb

end ContinuousFlexibility.Analysis
