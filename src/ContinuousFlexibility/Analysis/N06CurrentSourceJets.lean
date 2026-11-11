import ContinuousFlexibility.Analysis.N06CurrentInverseTestJets
import ContinuousFlexibility.Analysis.N06FiniteSourceGeometry
import ContinuousFlexibility.Analysis.N06WeakAngularLeibniz
import ContinuousFlexibility.Analysis.N06CanonicalProperties

/-!
# Actual angular source jets in the current coordinates

The angular inverse derivative is the adjugate vector field of the actual
forward chart. Iterating that physical vector field on `H * f / |J|`
produces the actual angular jets of the current canonical source. N04
gives smoothness of every one of these physical fields at the closed
physical piece, including its endpoints. Compactness therefore bounds
their pullbacks on the measured half-period tile. For a periodic source,
the same bound holds at every angle in the open canonical cylinder.

No value or regularity of the totalized inverse at a canonical boundary
is used. The constants here may depend on the current state, the piece,
the source and the finite angular order; no uniform smallness is claimed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual current source jets, kept on the physical side. -/
def n06PhysicalSourceAngularJet (F : PolarPoint → PolarPoint)
    (H f : PolarPoint → ℝ) : ℕ → PolarPoint → ℝ
  | 0 => fun x => H x * f x / |planeJacobian F x|
  | j + 1 => n06InverseChartDerivative F (0, 1)
      (n06PhysicalSourceAngularJet F H f j)

/-- Only forward-chart jets and its nonzero actual Jacobian are needed
to continue the source-jet recursion across a physical endpoint. -/
theorem n06PhysicalSourceAngularJet_contDiffAt
    {F : PolarPoint → PolarPoint} {H f : PolarPoint → ℝ} {x : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F x) (hH : ContDiffAt ℝ ∞ H x)
    (hJ : planeJacobian F x ≠ 0) (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) :
    ContDiffAt ℝ ∞ (n06PhysicalSourceAngularJet F H f j) x := by
  induction j with
  | zero =>
      have hd : ContDiffAt ℝ ∞ (fderiv ℝ F) x :=
        hF.fderiv_right (by simp)
      have hr : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (1, 0)) x :=
        hd.clm_apply contDiffAt_const
      have ht : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (0, 1)) x :=
        hd.clm_apply contDiffAt_const
      have hdet : ContDiffAt ℝ ∞ (planeJacobian F) x :=
        (hr.fst.mul ht.snd).sub (hr.snd.mul ht.fst)
      exact (hH.mul hf).div (hdet.abs hJ) (abs_ne_zero.mpr hJ)
  | succ j ih =>
      exact n06InverseChartDerivative_contDiffAt (0, 1) hF hJ ih

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Every angular jet of the actual current source is the pullback of
the corresponding physical adjugate derivative. Equality of preceding
jets is used on a neighborhood before differentiating. -/
theorem n06_current_canonicalSource_angularJet
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (m j : ℕ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative 0 j (canonicalSource S K z m f) p =
      n06PhysicalSourceAngularJet (K.chart z m) (K.height z m) f j
        (K.inverseChart z m p) := by
  have hc := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hb := h04.2.2.2.2.2.2.2.2.1 z hz hs m
  have hsource : ContDiffOn ℝ ∞ (canonicalSource S K z m f)
      (canonicalOpen S K m) :=
    n06_canonicalSource_contDiffOn (n06_N04_qualitative_parts h04).1
      hz hs hf.contDiffOn m
  induction j generalizing p with
  | zero =>
      simp only [mixedDerivative, iteratedDeriv_zero, canonicalSource,
        n06PhysicalSourceAngularJet]
  | succ j ih =>
      have he : mixedDerivative 0 j (canonicalSource S K z m f) =ᶠ[𝓝 p]
          (fun q => n06PhysicalSourceAngularJet (K.chart z m) (K.height z m) f j
            (K.inverseChart z m q)) := by
        filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
        exact ih hq
      have hx : (K.inverseChart z m p).1 ∈
          Icc (K.physicalLeft m) (K.physicalRight m) :=
        mem_Icc_of_Ioo (hc.2.1 hp).1
      have hg := n06PhysicalSourceAngularJet_contDiffAt
        (hb _ hx).1 (hb _ hx).2.1 (hb _ hx).2.2.1 hf.contDiffAt j
      calc
        mixedDerivative 0 (j + 1) (canonicalSource S K z m f) p =
            angularPartial (mixedDerivative 0 j (canonicalSource S K z m f)) p :=
          (n06_angularPartial_mixedAngular_on hsource j hp).symm
        _ = fderiv ℝ (fun q =>
            n06PhysicalSourceAngularJet (K.chart z m) (K.height z m) f j
              (K.inverseChart z m q)) p (0, 1) :=
          congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) (he.fderiv_eq (𝕜 := ℝ))
        _ = n06PhysicalSourceAngularJet (K.chart z m) (K.height z m) f (j + 1)
              (K.inverseChart z m p) :=
          n06_current_inverseChart_comp_fderiv h04 hz hs m (0, 1) hp
            (hg.differentiableAt (by simp))

/-- For any globally smooth physical source, all prescribed angular
orders have a bound on the actual measured half-period tile. This step
uses no periodicity of the source. -/
theorem n06_current_canonicalSource_angularJets_half_bounded
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (m b : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ j, j ≤ b →
      ∀ p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi,
        |mixedDerivative 0 j (canonicalSource S K z m f) p| ≤ B := by
  classical
  let Q : Set PolarPoint :=
    Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hb := h04.2.2.2.2.2.2.2.2.1 z hz hs m
  have hcontinuous (j : ℕ) :
      ContinuousOn (n06PhysicalSourceAngularJet (K.chart z m) (K.height z m) f j) Q := by
    intro x hx
    exact (n06PhysicalSourceAngularJet_contDiffAt
      (hb x hx.1).1 (hb x hx.1).2.1 (hb x hx.1).2.2.1 hf.contDiffAt j).continuousAt.continuousWithinAt
  have hbound : ∀ j : Fin (b + 1), ∃ c : ℝ, ∀ x ∈ Q,
      |n06PhysicalSourceAngularJet (K.chart z m) (K.height z m) f j.val x| ≤ c := by
    intro j
    obtain ⟨c, hc⟩ := hQ.bddAbove_image (hcontinuous j.val).abs
    exact ⟨c, fun x hx => hc ⟨x, hx, rfl⟩⟩
  choose c hc using hbound
  let B : ℝ := 1 + ∑ j : Fin (b + 1), |c j|
  have hsum : 0 ≤ ∑ j : Fin (b + 1), |c j| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B, by dsimp only [B]; linarith, ?_⟩
  intro j hj p hp
  let j' : Fin (b + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hx := (n06_canonicalChart_halfPeriod_maps h04 hz hs m).2 hp
  have hxQ : K.inverseChart z m p ∈ Q :=
    ⟨mem_Icc_of_Ioo hx.1, hx.2.1.le, hx.2.2⟩
  have hterm : |c j'| ≤ ∑ i : Fin (b + 1), |c i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ j')
  calc
    |mixedDerivative 0 j (canonicalSource S K z m f) p| =
        |n06PhysicalSourceAngularJet (K.chart z m) (K.height z m) f j
          (K.inverseChart z m p)| := by
      rw [n06_current_canonicalSource_angularJet h04 hz hs hf m j ⟨hp.1, mem_univ _⟩]
    _ ≤ c j' := hc j' _ hxQ
    _ ≤ |c j'| := le_abs_self _
    _ ≤ B := by dsimp only [B]; linarith

/-- Periodicity moves an arbitrary canonical angle into the measured
half-period tile. The inverse is still evaluated only at interior radial
points, including when the chosen angle is the period endpoint. -/
theorem n06_current_canonicalSource_angularJets_bounded
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hpF : Function.Periodic f (0, Real.pi)) (m b : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j (canonicalSource S K z m f) p| ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    n06_current_canonicalSource_angularJets_half_bounded h04 hz hs hf m b
  have hperiod : ∀ p ∈ canonicalOpen S K m,
      canonicalSource S K z m f (p + (0, Real.pi)) = canonicalSource S K z m f p :=
    fun p hp => n06_canonicalSource_periodicOn
      (n06_N04_qualitative_parts h04).1 hz hs (fun q _ => hpF q) m hp
  refine ⟨B, hB, ?_⟩
  intro j hj p hp
  have hjperiod : Function.Periodic
      (fun θ => mixedDerivative 0 j (canonicalSource S K z m f) (p.1, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using
      n06_mixedAngular_periodicOn hperiod j (p.1, θ) ⟨hp.1, mem_univ θ⟩
  obtain ⟨θ, hθ, heq⟩ := hjperiod.exists_mem_Ioc Real.pi_pos p.2 0
  have hθ' : θ ∈ Ioc (0 : ℝ) Real.pi := by simpa only [zero_add] using hθ
  calc
    |mixedDerivative 0 j (canonicalSource S K z m f) p| =
        |mixedDerivative 0 j (canonicalSource S K z m f) (p.1, θ)| := congrArg abs heq
    _ ≤ B := hbound j hj (p.1, θ) ⟨hp.1, hθ'⟩

end ContinuousFlexibility.Statements
