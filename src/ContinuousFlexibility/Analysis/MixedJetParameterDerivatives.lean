import ContinuousFlexibility.Analysis.MaterialDivergenceEnvelopes

/-!
# Parameter derivatives of actual spatial jets

The derivative assertion concerns the ordinary mixed derivatives of each
slice. Smoothness is needed only near the parameter under consideration.
Finite Leibniz sums and the exact partial-derivative identities preserve
this assertion without introducing a formal spatial jet.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

def MixedJetHasDerivAt (F : ℝ → PolarPoint → ℝ)
    (G : PolarPoint → ℝ) (t : ℝ) : Prop :=
  ∀ a b p, HasDerivAt (fun s => mixedDerivative a b (F s) p)
    (mixedDerivative a b G p) t

theorem MixedJetHasDerivAt.congr
    {F F' : ℝ → PolarPoint → ℝ} {G G' : PolarPoint → ℝ} {t : ℝ}
    (h : MixedJetHasDerivAt F G t)
    (hF : ∀ᶠ s in 𝓝 t, F s = F' s) (hG : G = G') :
    MixedJetHasDerivAt F' G' t := by
  subst G'
  intro a b p
  apply (h a b p).congr_of_eventuallyEq
  filter_upwards [hF] with s hs
  rw [hs]

theorem MixedJetHasDerivAt.add
    {F H : ℝ → PolarPoint → ℝ} {G K : PolarPoint → ℝ} {t : ℝ}
    (hF : ∀ᶠ s in 𝓝 t, ContDiff ℝ ∞ (F s))
    (hH : ∀ᶠ s in 𝓝 t, ContDiff ℝ ∞ (H s))
    (hG : ContDiff ℝ ∞ G) (hK : ContDiff ℝ ∞ K)
    (h : MixedJetHasDerivAt F G t) (h' : MixedJetHasDerivAt H K t) :
    MixedJetHasDerivAt (fun s p => F s p + H s p) (fun p => G p + K p) t := by
  intro a b p
  rw [mixedDerivative_add_of_contDiff hG hK]
  apply ((h a b p).add (h' a b p)).congr_of_eventuallyEq
  filter_upwards [hF, hH] with s hs hs'
  rw [mixedDerivative_add_of_contDiff hs hs']

theorem MixedJetHasDerivAt.mul_const
    {F : ℝ → PolarPoint → ℝ} {G u : PolarPoint → ℝ} {t : ℝ}
    (hF : ∀ᶠ s in 𝓝 t, ContDiff ℝ ∞ (F s))
    (hG : ContDiff ℝ ∞ G) (hu : ContDiff ℝ ∞ u)
    (h : MixedJetHasDerivAt F G t) :
    MixedJetHasDerivAt (fun s p => F s p * u p) (fun p => G p * u p) t := by
  intro a b p
  rw [mixedDerivative_mul hG hu]
  have hd : HasDerivAt
      (fun s => ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j (F s) p * mixedDerivative (a - i) (b - j) u p)
      (∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j G p * mixedDerivative (a - i) (b - j) u p) t :=
    HasDerivAt.fun_sum (fun j _ => HasDerivAt.fun_sum (fun i _ =>
      ((h i j p).const_mul ((b.choose j : ℝ) * (a.choose i : ℝ))).mul_const _))
  apply hd.congr_of_eventuallyEq
  filter_upwards [hF] with s hs
  rw [mixedDerivative_mul hs hu]

theorem MixedJetHasDerivAt.const_mul
    {F : ℝ → PolarPoint → ℝ} {G u : PolarPoint → ℝ} {t : ℝ}
    (hF : ∀ᶠ s in 𝓝 t, ContDiff ℝ ∞ (F s))
    (hG : ContDiff ℝ ∞ G) (hu : ContDiff ℝ ∞ u)
    (h : MixedJetHasDerivAt F G t) :
    MixedJetHasDerivAt (fun s p => u p * F s p) (fun p => u p * G p) t := by
  apply (MixedJetHasDerivAt.mul_const hF hG hu h).congr
  · exact Eventually.of_forall fun s => funext fun p => mul_comm _ _
  · exact funext fun p => mul_comm _ _

theorem MixedJetHasDerivAt.radialPartial
    {F : ℝ → PolarPoint → ℝ} {G : PolarPoint → ℝ} {t : ℝ}
    (hF : ∀ᶠ s in 𝓝 t, ContDiff ℝ ∞ (F s))
    (hG : ContDiff ℝ ∞ G) (h : MixedJetHasDerivAt F G t) :
    MixedJetHasDerivAt (fun s => ContinuousFlexibility.Statements.radialPartial (F s)) (ContinuousFlexibility.Statements.radialPartial G) t := by
  intro a b p
  rw [mixedDerivative_radialPartial isOpen_univ hG.contDiffOn a b (mem_univ p)]
  apply (h (a + 1) b p).congr_of_eventuallyEq
  filter_upwards [hF] with s hs
  rw [mixedDerivative_radialPartial isOpen_univ hs.contDiffOn a b (mem_univ p)]

theorem MixedJetHasDerivAt.angularPartial
    {F : ℝ → PolarPoint → ℝ} {G : PolarPoint → ℝ} {t : ℝ}
    (hF : ∀ᶠ s in 𝓝 t, ContDiff ℝ ∞ (F s))
    (hG : ContDiff ℝ ∞ G) (h : MixedJetHasDerivAt F G t) :
    MixedJetHasDerivAt (fun s => ContinuousFlexibility.Statements.angularPartial (F s)) (ContinuousFlexibility.Statements.angularPartial G) t := by
  intro a b p
  rw [mixedDerivative_angularPartial isOpen_univ hG.contDiffOn a b (mem_univ p)]
  apply (h a (b + 1) p).congr_of_eventuallyEq
  filter_upwards [hF] with s hs
  rw [mixedDerivative_angularPartial isOpen_univ hs.contDiffOn a b (mem_univ p)]

end ContinuousFlexibility.Statements
