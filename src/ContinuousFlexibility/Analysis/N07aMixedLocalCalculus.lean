module

public import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets
public import ContinuousFlexibility.Analysis.SpacesHeightAlgebra

/-!
# Mixed derivative identities on the actual open domain

The reconstructed unknown and the reciprocal leading coefficient are
smooth on an open piece. The local identities below differentiate them
there without demanding a smooth global extension across an endpoint.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n07a_mixedDerivative_eventuallyEq {f g : PolarPoint → ℝ} {p : PolarPoint}
    (he : f =ᶠ[𝓝 p] g) (a b : ℕ) : mixedDerivative a b f p = mixedDerivative a b g p := by
  rw [show p = (p.1, p.2) from rfl, nhds_prod_eq] at he
  obtain ⟨P, hP, Q, hQ, h⟩ := eventually_prod_iff.mp he
  have houter : (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun r => iteratedDeriv b (fun θ => g (r, θ)) p.2) := by
    filter_upwards [hP] with r hr
    have hinner : (fun θ => f (r, θ)) =ᶠ[𝓝 p.2] (fun θ => g (r, θ)) := by
      filter_upwards [hQ] with θ hθ
      exact h hr hθ
    exact hinner.iteratedDeriv_eq b
  exact houter.iteratedDeriv_eq a

theorem n07a_mixedDerivative_eqOn {U : Set PolarPoint} (hU : IsOpen U)
    {f g : PolarPoint → ℝ} (he : EqOn f g U) (a b : ℕ) :
    EqOn (mixedDerivative a b f) (mixedDerivative a b g) U := by
  intro p hp
  apply n07a_mixedDerivative_eventuallyEq _ a b
  filter_upwards [hU.mem_nhds hp] with q hq
  exact he hq

private theorem n07a_angularSlice_contDiffAt {U : Set PolarPoint} (hU : IsOpen U)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) {r θ : ℝ} (hp : (r, θ) ∈ U) :
    ContDiffAt ℝ ∞ (fun t => f (r, t)) θ :=
  (hf.contDiffAt (hU.mem_nhds hp)).comp θ (contDiffAt_const.prodMk contDiffAt_id)

private theorem n07a_angularJet_radialSlice_contDiffAt {U : Set PolarPoint}
    (hU : IsOpen U) {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (j : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    ContDiffAt ℝ ∞ (fun r => iteratedDeriv j (fun θ => f (r, θ)) p.2) p.1 := by
  have h := ((contDiffOn_mixedDerivative hU hf 0 j).contDiffAt (hU.mem_nhds hp)).comp
    p.1 (contDiffAt_id.prodMk contDiffAt_const)
  simpa only [Function.comp_def, id_eq, mixedDerivative, iteratedDeriv_zero] using h

theorem n07a_mixedDerivative_sum_on {ι : Type*} {U : Set PolarPoint}
    (hU : IsOpen U) {I : Finset ι} {f : ι → PolarPoint → ℝ}
    (hf : ∀ i ∈ I, ContDiffOn ℝ ∞ (f i) U) (a b : ℕ)
    {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b (fun q => ∑ i ∈ I, f i q) p =
      ∑ i ∈ I, mixedDerivative a b (f i) p := by
  have hrows : ∀ᶠ r in 𝓝 p.1, (r, p.2) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
  have he : (fun r => iteratedDeriv b (fun θ => ∑ i ∈ I, f i (r, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun r => ∑ i ∈ I, iteratedDeriv b (fun θ => f i (r, θ)) p.2) := by
    filter_upwards [hrows] with r hr
    exact iteratedDeriv_fun_sum (fun i hi =>
      (n07a_angularSlice_contDiffAt hU (hf i hi) hr).of_le (by simp))
  unfold mixedDerivative
  rw [he.iteratedDeriv_eq a]
  exact iteratedDeriv_fun_sum (fun i hi =>
    (n07a_angularJet_radialSlice_contDiffAt hU (hf i hi) b hp).of_le (by simp))

theorem n07a_mixedDerivative_add_on {U : Set PolarPoint} (hU : IsOpen U)
    {f g : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b (fun q => f q + g q) p =
      mixedDerivative a b f p + mixedDerivative a b g p := by
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      ContDiffOn ℝ ∞ (![f, g] i) U := by
    intro i _
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> assumption
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
    n07a_mixedDerivative_sum_on hU hs a b hp

theorem n07a_mixedDerivative_mul_on {U : Set PolarPoint} (hU : IsOpen U)
    {f g : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b (fun q => f q * g q) p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j f p * mixedDerivative (a - i) (b - j) g p := by
  have hfr (j : ℕ) := n07a_angularJet_radialSlice_contDiffAt hU hf j hp
  have hgr (j : ℕ) := n07a_angularJet_radialSlice_contDiffAt hU hg j hp
  have hrows : ∀ᶠ r in 𝓝 p.1, (r, p.2) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
  have he : (fun r => iteratedDeriv b (fun θ => f (r, θ) * g (r, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun r => ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) *
        (iteratedDeriv j (fun θ => f (r, θ)) p.2 *
          iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2)) := by
    filter_upwards [hrows] with r hr
    simpa only [mul_assoc] using iteratedDeriv_fun_mul
      ((n07a_angularSlice_contDiffAt hU hf hr).of_le (by simp))
      ((n07a_angularSlice_contDiffAt hU hg hr).of_le (by simp))
  unfold mixedDerivative
  rw [he.iteratedDeriv_eq a, iteratedDeriv_fun_sum (fun j _ =>
    ((contDiffAt_const.mul ((hfr j).mul (hgr (b - j)))).of_le (by simp)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul ((hfr j).of_le (by simp)) ((hgr (b - j)).of_le (by simp)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem n07a_radialPartial_mixedDerivative_on {U : Set PolarPoint} (hU : IsOpen U)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) (a b : ℕ)
    {p : PolarPoint} (hp : p ∈ U) :
    radialPartial (mixedDerivative a b f) p = mixedDerivative (a + 1) b f p := by
  have hd := (((contDiffOn_mixedDerivative hU hf a b).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hs := hd.comp_hasDerivAt p.1
    ((hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2))
  have he : deriv (fun r => mixedDerivative a b f (r, p.2)) p.1 =
      radialPartial (mixedDerivative a b f) p := hs.deriv
  rw [← he]
  simp only [mixedDerivative, iteratedDeriv_succ]

theorem n07a_angularPartial_zero_mixedDerivative_on {U : Set PolarPoint} (hU : IsOpen U)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) (b : ℕ)
    {p : PolarPoint} (hp : p ∈ U) :
    angularPartial (mixedDerivative 0 b f) p = mixedDerivative 0 (b + 1) f p := by
  have hd := (((contDiffOn_mixedDerivative hU hf 0 b).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hs := hd.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2))
  have he : deriv (fun θ => mixedDerivative 0 b f (p.1, θ)) p.2 =
      angularPartial (mixedDerivative 0 b f) p := hs.deriv
  rw [← he]
  simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_succ]

theorem n07a_mixedDerivative_mixedDerivative_on {U : Set PolarPoint} (hU : IsOpen U)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U) (a b c d : ℕ) :
    EqOn (mixedDerivative a b (mixedDerivative c d f))
      (mixedDerivative (a + c) (b + d) f) U := by
  induction c generalizing a with
  | zero =>
    induction d generalizing b with
    | zero =>
      simp only [spaces_mixedDerivative_zero, Nat.add_zero]
      exact fun _ _ => rfl
    | succ d ih =>
      have he : EqOn (mixedDerivative 0 (d + 1) f)
          (angularPartial (mixedDerivative 0 d f)) U := by
        intro p hp
        exact (n07a_angularPartial_zero_mixedDerivative_on hU hf d hp).symm
      intro p hp
      rw [n07a_mixedDerivative_eqOn hU he a b hp,
        mixedDerivative_angularPartial hU (contDiffOn_mixedDerivative hU hf 0 d) a b hp,
        ih (b + 1) hp]
      congr 1
      omega
  | succ c ih =>
    have he : EqOn (mixedDerivative (c + 1) d f)
        (radialPartial (mixedDerivative c d f)) U := by
      intro p hp
      exact (n07a_radialPartial_mixedDerivative_on hU hf c d hp).symm
    intro p hp
    rw [n07a_mixedDerivative_eqOn hU he a b hp,
      mixedDerivative_radialPartial hU (contDiffOn_mixedDerivative hU hf c d) a b hp,
      ih (a + 1) hp]
    congr 1
    omega

end ContinuousFlexibility.Analysis
