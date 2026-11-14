module

public import ContinuousFlexibility.Analysis.N06CurrentPositiveOperatorTest
public import ContinuousFlexibility.Analysis.N06EllipticConjugationProbes
public import ContinuousFlexibility.Analysis.N06CurrentOperatorReflection

/-!
# True current operator linearity and reflection averaging

Canonical principal coefficients are smooth on the positive pieces by
the actual elliptic recovery theorem, and on negative pieces they are
the recorded polynomial normal form. The original operator identity
therefore proves linearity for arbitrary smooth physical tests, even
without global differentiability of the bare physical coefficients.

Reflection covariance is a separate exact identity: reflection is a
continuous linear equivalence, so the totalized derivatives transform
correctly without any coefficient regularity assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Reflection covariance for arbitrary inputs, including tests with no
parity. The three actual coefficient signs suffice. -/
theorem n06_divergenceOperator_reflection
    {A : SymmetricCoefficients}
    (ha : ∀ p : PolarPoint, A.a (p.1, -p.2) = A.a p)
    (hb : ∀ p : PolarPoint, A.b (p.1, -p.2) = -A.b p)
    (hc : ∀ p : PolarPoint, A.c (p.1, -p.2) = A.c p)
    (f : PolarPoint → ℝ) (p : PolarPoint) :
    divergenceOperator A (fun q => f (q.1, -q.2)) p =
      divergenceOperator A f (p.1, -p.2) := by
  let N : PolarPoint → ℝ := fun q => A.a q * radialPartial f q + A.b q * angularPartial f q
  let T : PolarPoint → ℝ := fun q => A.b q * radialPartial f q + A.c q * angularPartial f q
  have hN : (fun q => A.a q * radialPartial (fun x => f (x.1, -x.2)) q +
      A.b q * angularPartial (fun x => f (x.1, -x.2)) q) =
        fun q => N (q.1, -q.2) := by
    funext q
    simp only [N, n06_radialPartial_comp_reflection, n06_angularPartial_comp_reflection,
      ha q, hb q]
    ring
  have hT : (fun q => A.b q * radialPartial (fun x => f (x.1, -x.2)) q +
      A.c q * angularPartial (fun x => f (x.1, -x.2)) q) =
        fun q => -T (q.1, -q.2) := by
    funext q
    simp only [T, n06_radialPartial_comp_reflection, n06_angularPartial_comp_reflection,
      hb q, hc q]
    ring
  change radialPartial _ p + angularPartial _ p =
    radialPartial N (p.1, -p.2) + angularPartial T (p.1, -p.2)
  rw [hN, hT, n06_radialPartial_comp_reflection]
  have ht : angularPartial (fun q => -T (q.1, -q.2)) p =
      -angularPartial (fun q => T (q.1, -q.2)) p := by
    simp only [angularPartial, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  rw [ht, n06_angularPartial_comp_reflection, neg_neg]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- Only the positive branch needs the recovered regularity; the actual
negative normal form supplies its own smooth coefficient germs. -/
theorem n06_current_canonicalCoefficient_germs
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hpositive : K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    ContDiffAt ℝ ∞ (K.coefficients z m).a p ∧
      ContDiffAt ℝ ∞ (K.coefficients z m).b p ∧
      ContDiffAt ℝ ∞ (K.coefficients z m).c p := by
  have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  cases hm : K.positive m
  · have he : ∀ᶠ q in 𝓝 p,
        (K.coefficients z m).a q = 1 ∧ (K.coefficients z m).b q = 0 ∧
          (K.coefficients z m).c q = -q.1 := by
      filter_upwards [hn] with q hq
      exact ((n06_N04_qualitative_parts h04).2).2.2.2.1 z hz hs m hm q hq
    exact ⟨contDiffAt_const.congr_of_eventuallyEq (he.mono fun _ h => h.1),
      contDiffAt_const.congr_of_eventuallyEq (he.mono fun _ h => h.2.1),
      contDiffAt_fst.neg.congr_of_eventuallyEq (he.mono fun _ h => h.2.2)⟩
  · exact ⟨(hpositive hm).1.contDiffAt hn, (hpositive hm).2.1.contDiffAt hn,
      (hpositive hm).2.2.contDiffAt hn⟩

/-- The real current source transform intertwines actual add/smul with
the smooth canonical differential expression. -/
theorem n06_current_source_divergence_add_smul
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hpositive : K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {f g : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (s : ℝ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (fun q => f q + s * g q)) p =
      canonicalSource S K z m (divergenceOperator (L.coefficients z) f) p +
        s * canonicalSource S K z m (divergenceOperator (L.coefficients z) g) p := by
  have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hcoef := n06_current_canonicalCoefficient_germs h04 hz hs hpositive hp
  have hfg : ContDiff ℝ ∞ (fun q => f q + s * g q) := hf.add (contDiff_const.mul hg)
  have he : canonicalHeight S K z m (fun q => f q + s * g q) =
      fun q => canonicalHeight S K z m f q + s * canonicalHeight S K z m g q := by
    funext q
    simp only [canonicalHeight]
    ring
  rw [n06_current_source_operatorTest_eq h04 hz hs hfg hp,
    n06_current_source_operatorTest_eq h04 hz hs hf hp,
    n06_current_source_operatorTest_eq h04 hz hs hg hp, he,
    n06_divergenceOperator_add_smul hcoef.1 hcoef.2.1 hcoef.2.2
      ((n06_current_canonicalHeight_contDiffOn h04 hz hs m hf).contDiffAt hn)
      ((n06_current_canonicalHeight_contDiffOn h04 hz hs m hg).contDiffAt hn) s]
  ring

/-- On an actual physical piece, the height/Jacobian factor is nonzero.
Cancelling it gives actual physical operator linearity, without assuming
global smoothness of the bare corrected b or c fields. -/
theorem n06_current_divergence_add_smul_on_piece
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hpositive : K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {f g : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (s : ℝ)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    divergenceOperator (L.coefficients z) (fun q => f q + s * g q) p =
      divergenceOperator (L.coefficients z) f p + s * divergenceOperator (L.coefficients z) g p := by
  have hc := h04.1.charts z hz hs m
  have he := n06_current_source_divergence_add_smul h04 hz hs hpositive hf hg s (hc.1 hp)
  let w : ℝ := K.height z m p / |planeJacobian (K.chart z m) p|
  have hw : w ≠ 0 := div_ne_zero (hc.2.2.2.2.2.2.2 p hp).1.ne'
    (abs_ne_zero.mpr (hc.2.2.2.2.2.2.2 p hp).2.1)
  have hsource (v : PolarPoint → ℝ) : canonicalSource S K z m v (K.chart z m p) = w * v p := by
    simp only [canonicalSource, hc.2.2.1 p hp, w]
    ring
  rw [hsource, hsource, hsource] at he
  apply mul_left_cancel₀ hw
  calc
    _ = w * divergenceOperator (L.coefficients z) f p +
        s * (w * divergenceOperator (L.coefficients z) g p) := he
    _ = _ := by ring

/-- Reflection averaging commutes with the actual operator on every
piece, for an arbitrary smooth test. N03 supplies the actual parity signs. -/
theorem n06_current_divergence_reflectionAverage_on_piece
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hpositive : K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    divergenceOperator (L.coefficients z) (fun q => (f q + f (q.1, -q.2)) / 2) p =
      (divergenceOperator (L.coefficients z) f p +
        divergenceOperator (L.coefficients z) f (p.1, -p.2)) / 2 := by
  let g : PolarPoint → ℝ := fun q => f (q.1, -q.2)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_fst.prodMk contDiff_snd.neg)
  have hsum : ContDiff ℝ ∞ (fun q => f q + (1 : ℝ) * g q) :=
    hf.add (contDiff_const.mul hg)
  have he : (fun q => (f q + f (q.1, -q.2)) / 2) =
      fun q => (0 : ℝ) + (1 / 2 : ℝ) * (f q + (1 : ℝ) * g q) := by
    funext q
    dsimp only [g]
    ring
  rw [he, n06_current_divergence_add_smul_on_piece h04 hz hs hpositive contDiff_const hsum
      (1 / 2 : ℝ) hp, divergenceOperator_const, zero_add,
    n06_current_divergence_add_smul_on_piece h04 hz hs hpositive hf hg 1 hp, one_mul]
  have href := n06_divergenceOperator_reflection
    (fun q => (h03.2.2.2.1 z hz hs q.1 q.2).1)
    (fun q => (h03.2.2.2.1 z hz hs q.1 q.2).2.1)
    (fun q => (h03.2.2.2.1 z hz hs q.1 q.2).2.2) f p
  change divergenceOperator (L.coefficients z) g p =
    divergenceOperator (L.coefficients z) f (p.1, -p.2) at href
  rw [href]
  ring

end ContinuousFlexibility.Statements
