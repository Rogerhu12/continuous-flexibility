import ContinuousFlexibility.Analysis.N06CanonicalDifference

/-!
# The sign of the actual positive canonical perturbation

The frozen cubic factorization is used as an equality of coefficient
germs. Local differentiability of the reference and divided coefficients
then identifies the true differential difference. In the positive
canonical operator its sign is minus, while the potential difference
has sign plus.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- A smooth reference and differentiable divided coefficients determine
the current coefficient derivatives through the actual cubic germ. -/
theorem n06_divergenceDifference_eq_cubic_of_germ
    {L L₀ : SymmetricCoefficients} {d A B C u : PolarPoint → ℝ} {p : PolarPoint}
    (ha₀ : DifferentiableAt ℝ L₀.a p) (hb₀ : DifferentiableAt ℝ L₀.b p)
    (hc₀ : DifferentiableAt ℝ L₀.c p)
    (hd : DifferentiableAt ℝ d p) (hA : DifferentiableAt ℝ A p)
    (hB : DifferentiableAt ℝ B p) (hC : DifferentiableAt ℝ C p)
    (hu : ContDiffAt ℝ 2 u p)
    (heqa : (fun q => L.a q - L₀.a q) =ᶠ[𝓝 p] (fun q => d q ^ 3 * A q))
    (heqb : (fun q => L.b q - L₀.b q) =ᶠ[𝓝 p] (fun q => d q ^ 3 * B q))
    (heqc : (fun q => L.c q - L₀.c q) =ᶠ[𝓝 p] (fun q => d q ^ 3 * C q)) :
    divergenceOperator L u p - divergenceOperator L₀ u p =
      divergenceOperator (n06CubicCoefficients d A B C) u p := by
  have hda : DifferentiableAt ℝ L.a p :=
    (ha₀.add ((hd.pow 3).mul hA)).congr_of_eventuallyEq
      (heqa.mono (fun q h => by
        change L.a q = L₀.a q + d q ^ 3 * A q
        linarith only [h]))
  have hdb : DifferentiableAt ℝ L.b p :=
    (hb₀.add ((hd.pow 3).mul hB)).congr_of_eventuallyEq
      (heqb.mono (fun q h => by
        change L.b q = L₀.b q + d q ^ 3 * B q
        linarith only [h]))
  have hdc : DifferentiableAt ℝ L.c p :=
    (hc₀.add ((hd.pow 3).mul hC)).congr_of_eventuallyEq
      (heqc.mono (fun q h => by
        change L.c q = L₀.c q + d q ^ 3 * C q
        linarith only [h]))
  rw [n06_divergenceOperator_sub hda hdb hdc ha₀ hb₀ hc₀ hu]
  exact n06_divergenceOperator_congr_germ u heqa heqb heqc

/-- On each positive piece the principal relative term is the negative
of the cubic divergence source constructed by the weak graph argument. -/
theorem n06_positive_canonicalOperator_difference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hN04 : N04Properties D T S C L K base loss ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (href : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {m : ℕ} (hm : K.positive m = true)
    (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m)
    (ha₀ : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).a p)
    (hb₀ : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).b p)
    (hc₀ : DifferentiableAt ℝ (K.coefficients (C.referenceState, 0) m).c p)
    (hA : DifferentiableAt ℝ (K.dividedDifference z m).a p)
    (hB : DifferentiableAt ℝ (K.dividedDifference z m).b p)
    (hC : DifferentiableAt ℝ (K.dividedDifference z m).c p) :
    canonicalOperator S K L z m W p -
        canonicalOperator S K L (C.referenceState, 0) m W p =
      -divergenceOperator
        (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
          (K.dividedDifference z m).a (K.dividedDifference z m).b
          (K.dividedDifference z m).c) W p +
        (K.potential z m p - K.potential (C.referenceState, 0) m p) * W p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hop, _, hcubic, _, _⟩ := hN04
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q ∈ canonicalOpen S K m :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hg := hnear.mono (fun q hq => hcubic z hz hsector m hm q hq)
  have hd : DifferentiableAt ℝ
      (fun q : PolarPoint => (q.1 - K.left m) * (K.right m - q.1)) p :=
    ((differentiableAt_fst.sub (differentiableAt_const (K.left m))).mul
      ((differentiableAt_const (K.right m)).sub differentiableAt_fst))
  have hdiv := n06_divergenceDifference_eq_cubic_of_germ ha₀ hb₀ hc₀ hd hA hB hC
    (hW.contDiffAt.of_le (by simp)) (hg.mono (fun _ h => h.1))
      (hg.mono (fun _ h => h.2.1)) (hg.mono (fun _ h => h.2.2))
  have hcur : canonicalOperator S K L z m W p =
      -divergenceOperator (K.coefficients z m) W p + K.potential z m p * W p := by
    simpa [hm] using hop z hz hsector m W hW p hp
  have hstar : canonicalOperator S K L (C.referenceState, 0) m W p =
      -divergenceOperator (K.coefficients (C.referenceState, 0) m) W p +
        K.potential (C.referenceState, 0) m p * W p := by
    simpa [hm] using
      hop (C.referenceState, 0) hz₀ href m W hW p hp
  rw [hcur, hstar]
  calc
    _ = -(divergenceOperator (K.coefficients z m) W p -
        divergenceOperator (K.coefficients (C.referenceState, 0) m) W p) +
        (K.potential z m p - K.potential (C.referenceState, 0) m p) * W p := by ring
    _ = _ := by rw [hdiv]

end ContinuousFlexibility.Statements
