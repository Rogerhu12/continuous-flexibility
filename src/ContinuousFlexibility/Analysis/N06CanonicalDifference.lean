import ContinuousFlexibility.Analysis.N06CubicDifferential

/-!
# Actual coefficient differences supplied by N04

On negative pieces the principal differential expression is fixed, so
the canonical perturbation is exactly multiplication by the potential
difference. On positive pieces the divided coefficients and all their
interior spatial jets vanish at the reference state. These conclusions
use the stated coordinate identities, without adding coefficient bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A field which vanishes on a whole radial strip has every mixed jet zero
at its interior points, independently of its values outside that strip. -/
theorem n06_mixedDerivative_eq_zero_on_strip {f : PolarPoint → ℝ} {l r : ℝ}
    (hf : ∀ p : PolarPoint, p.1 ∈ Ioo l r → f p = 0)
    (a b : ℕ) {p : PolarPoint} (hp : p.1 ∈ Ioo l r) :
    mixedDerivative a b f p = 0 := by
  have hangular (y : ℝ) (hy : y ∈ Ioo l r) :
      (fun θ => f (y, θ)) = (fun _ : ℝ => (0 : ℝ)) :=
    funext (fun θ => hf (y, θ) hy)
  have hr : (fun y => iteratedDeriv b (fun θ => f (y, θ)) p.2)
      =ᶠ[𝓝 p.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with y hy
    rw [hangular y hy]
    exact iteratedDeriv_fun_const_zero
  simpa only [mixedDerivative, iteratedDeriv_fun_const_zero] using hr.iteratedDeriv_eq a

private theorem n06_seminorm_center {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) : p (x - x) < ε := by
  simpa only [sub_self, map_zero] using hε

private theorem n06_reference_neighborhood {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  constructor
  · exact n06_seminorm_center (stateGrading S base) C.referenceState hε
  · simpa only [abs_zero] using hε

/-- The divided principal coefficients are genuinely zero at the reference
state; this follows from the cubic factorization on the open positive piece. -/
theorem n06_positive_dividedDifference_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hN04 : N04Properties D T S C L K base loss ε) (hε : 0 < ε)
    (href : stateSector S C.referenceState) {m : ℕ} (hm : K.positive m = true)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    (K.dividedDifference (C.referenceState, 0) m).a p = 0 ∧
    (K.dividedDifference (C.referenceState, 0) m).b p = 0 ∧
    (K.dividedDifference (C.referenceState, 0) m).c p = 0 := by
  have hcubic := hN04.2.1.2.2.2.2
  obtain ⟨ha, hb, hc⟩ := hcubic (C.referenceState, 0)
    (n06_reference_neighborhood C base hε) href m hm p hp
  have hd : ((p.1 - K.left m) * (K.right m - p.1)) ^ 3 ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (mul_pos (sub_pos.mpr hp.1.1) (sub_pos.mpr hp.1.2)))
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (by simpa only [sub_self] using ha.symm)).resolve_left hd
  · exact (mul_eq_zero.mp (by simpa only [sub_self] using hb.symm)).resolve_left hd
  · exact (mul_eq_zero.mp (by simpa only [sub_self] using hc.symm)).resolve_left hd

theorem n06_positive_dividedDifference_reference_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hN04 : N04Properties D T S C L K base loss ε) (hε : 0 < ε)
    (href : stateSector S C.referenceState) {m : ℕ} (hm : K.positive m = true)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative a b (K.dividedDifference (C.referenceState, 0) m).a p = 0 ∧
    mixedDerivative a b (K.dividedDifference (C.referenceState, 0) m).b p = 0 ∧
    mixedDerivative a b (K.dividedDifference (C.referenceState, 0) m).c p = 0 := by
  have hz (q : PolarPoint) (hq : q.1 ∈ Ioo (K.left m) (K.right m)) :=
    n06_positive_dividedDifference_reference hN04 hε href hm
      (show q ∈ canonicalOpen S K m from ⟨hq, mem_univ _⟩)
  exact ⟨n06_mixedDerivative_eq_zero_on_strip (fun q hq => (hz q hq).1) a b hp.1,
    n06_mixedDerivative_eq_zero_on_strip (fun q hq => (hz q hq).2.1) a b hp.1,
    n06_mixedDerivative_eq_zero_on_strip (fun q hq => (hz q hq).2.2) a b hp.1⟩

/-- On a negative piece the actual differential operator difference has no
principal part, including when its coefficients are differentiated. -/
theorem n06_negative_canonicalOperator_difference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hN04 : N04Properties D T S C L K base loss ε) (hε : 0 < ε)
    (href : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {m : ℕ} (hm : K.positive m = false)
    (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalOperator S K L z m W p -
        canonicalOperator S K L (C.referenceState, 0) m W p =
      (K.potential z m p - K.potential (C.referenceState, 0) m p) * W p := by
  have hop := hN04.2.1.2.2.1
  have hneg := hN04.2.1.2.2.2.1
  have hzero := n06_reference_neighborhood C base hε
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q ∈ canonicalOpen S K m :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hg : ∀ᶠ q : PolarPoint in 𝓝 p,
      (K.coefficients z m).a q = (K.coefficients (C.referenceState, 0) m).a q ∧
      (K.coefficients z m).b q = (K.coefficients (C.referenceState, 0) m).b q ∧
      (K.coefficients z m).c q = (K.coefficients (C.referenceState, 0) m).c q := by
    filter_upwards [hnear] with q hq
    have hcur := hneg z hz hsector m hm q hq
    have hstar := hneg (C.referenceState, 0) hzero href m hm q hq
    exact ⟨hcur.1.trans hstar.1.symm, hcur.2.1.trans hstar.2.1.symm,
      hcur.2.2.trans hstar.2.2.symm⟩
  have hdiv := n06_divergenceOperator_congr_germ W
    (hg.mono (fun _ h => h.1)) (hg.mono (fun _ h => h.2.1))
    (hg.mono (fun _ h => h.2.2))
  rw [hop z hz hsector m W hW p hp,
    hop (C.referenceState, 0) hzero href m W hW p hp, hdiv]
  ring

end ContinuousFlexibility.Statements
