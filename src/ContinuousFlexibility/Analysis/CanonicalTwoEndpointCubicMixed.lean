import ContinuousFlexibility.Analysis.CanonicalTwoEndpointCubic
import ContinuousFlexibility.Analysis.CanonicalCubicJets

/-!
# Mixed jets of cubic division at both ends of a cylinder

The two divisions use the same one-endpoint theorem, with radial reflection
for the second endpoint.  Actual vanishing slice jets are transported through
the first division.  The resulting estimate loses six radial derivatives and
has constant `1 / 36`, independent of the angular order and interval length.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

def reflectRadialField (R : ℝ) (F : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  F (R - p.1, p.2)

theorem contDiff_reflectRadialField (R : ℝ) {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (reflectRadialField R F) :=
  hF.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)

/-- Radial reflection preserves angular differentiation and contributes
exactly one minus sign for each radial derivative. -/
theorem mixedDerivative_reflectRadialField (R : ℝ) (F : PolarPoint → ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (reflectRadialField R F) p =
      (-1 : ℝ) ^ a * mixedDerivative a b F (R - p.1, p.2) := by
  simpa only [mixedDerivative, reflectRadialField, smul_eq_mul] using
    congrFun (iteratedDeriv_comp_const_sub a
      (fun r : ℝ => iteratedDeriv b (fun θ : ℝ => F (r, θ)) p.2) R) p.1

theorem abs_mixedDerivative_reflectRadialField (R : ℝ) (F : PolarPoint → ℝ)
    (a b : ℕ) (p : PolarPoint) :
    |mixedDerivative a b (reflectRadialField R F) p| =
      |mixedDerivative a b F (R - p.1, p.2)| := by
  rw [mixedDerivative_reflectRadialField]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- Ordinary jets of the radial slices are the genuine boundary partials. -/
theorem radialBoundaryPartials_of_sliceJets {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (R : ℝ)
    (h : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun r : ℝ => F (r, θ)) R = 0) :
    (∀ θ : ℝ, F (R, θ) = 0) ∧
      (∀ θ : ℝ, radialPartial F (R, θ) = 0) ∧
      (∀ θ : ℝ, radialPartial (radialPartial F) (R, θ) = 0) := by
  have hz : mixedDerivative 0 0 F = F := by
    funext p
    simp only [mixedDerivative, iteratedDeriv_zero]
  have hrad : radialPartial F = mixedDerivative 1 0 F := by
    simpa only [hz, Nat.zero_add] using radialPartial_mixedDerivative hF 0 0
  have hrad2 : radialPartial (radialPartial F) = mixedDerivative 2 0 F := by
    simpa only [← hrad] using radialPartial_mixedDerivative hF 1 0
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    simpa only [iteratedDeriv_zero] using h θ 0 (by decide)
  · intro θ
    rw [hrad]
    simpa only [mixedDerivative, iteratedDeriv_zero] using h θ 1 (by decide)
  · intro θ
    rw [hrad2]
    simpa only [mixedDerivative, iteratedDeriv_zero] using h θ 2 le_rfl

/-- The first division preserves the right endpoint jets, and reflection
moves these actual zero jets to the origin for the second division. -/
theorem reflectedRadialCubicQuotient_zero_jets {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) {R : ℝ} (hR : 0 < R)
    (hleft : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun r : ℝ => F (r, θ)) 0 = 0)
    (hright : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun r : ℝ => F (r, θ)) R = 0) :
    ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun r : ℝ =>
        reflectRadialField R (radialCubicQuotient F) (r, θ)) 0 = 0 := by
  intro θ i hi
  have hs : ContDiff ℝ ∞ (fun r : ℝ => F (r, θ)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have h0 : F (0, θ) = 0 := by
    simpa only [iteratedDeriv_zero] using hleft θ 0 (by decide)
  have h1 : deriv (fun r : ℝ => F (r, θ)) 0 = 0 := by
    simpa only [iteratedDeriv_one] using hleft θ 1 (by decide)
  have h2 : iteratedDeriv 2 (fun r : ℝ => F (r, θ)) 0 = 0 := hleft θ 2 le_rfl
  have hqi := cubicQuotient_zero_jet_of_zero_jets hs h0 h1 h2 hR.ne' i
    (fun j hj => hright θ j (hj.trans hi))
  change iteratedDeriv i
    (fun r : ℝ => cubicQuotient (fun t : ℝ => F (t, θ)) (R - r)) 0 = 0
  rw [iteratedDeriv_comp_const_sub]
  simp only [sub_zero, hqi, smul_zero]

/-- The regularized quotient on a cylinder with radial endpoints zero and R. -/
def radialTwoEndpointCubicQuotient (F : PolarPoint → ℝ) (R : ℝ) : PolarPoint → ℝ :=
  reflectRadialField R
    (radialCubicQuotient (reflectRadialField R (radialCubicQuotient F)))

theorem radialTwoEndpointCubicQuotient_eq_div (F : PolarPoint → ℝ)
    {R : ℝ} {p : PolarPoint} (hp : p.1 ∈ Ioo (0 : ℝ) R) :
    radialTwoEndpointCubicQuotient F R p = F p / (p.1 * (R - p.1)) ^ 3 := by
  change twoEndpointCubicQuotient (fun r : ℝ => F (r, p.2)) R p.1 = _
  exact twoEndpointCubicQuotient_eq_div _ hp

/-- Both removable boundaries are jointly smooth in radial and angular variables. -/
theorem contDiff_radialTwoEndpointCubicQuotient {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) {R : ℝ} (hR : 0 < R)
    (hleft : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun r : ℝ => F (r, θ)) 0 = 0)
    (hright : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun r : ℝ => F (r, θ)) R = 0) :
    ContDiff ℝ ∞ (radialTwoEndpointCubicQuotient F R) := by
  obtain ⟨h0, h1, h2⟩ := radialBoundaryPartials_of_sliceJets hF 0 hleft
  have hq := contDiff_radialCubicQuotient hF h0 h1 h2
  have hg := contDiff_reflectRadialField R hq
  obtain ⟨hg0, hg1, hg2⟩ := radialBoundaryPartials_of_sliceJets hg 0
    (reflectedRadialCubicQuotient_zero_jets hF hR hleft hright)
  exact contDiff_reflectRadialField R (contDiff_radialCubicQuotient hg hg0 hg1 hg2)

/-- Mixed differentiation costs six radial derivatives and no additional
angular derivatives.  The constant does not depend on either order or on R. -/
theorem abs_mixedDerivative_radialTwoEndpointCubicQuotient_le
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) {R : ℝ} (hR : 0 < R)
    (hleft : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun r : ℝ => F (r, θ)) 0 = 0)
    (hright : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun r : ℝ => F (r, θ)) R = 0)
    (a b : ℕ) {M : ℝ} {p : PolarPoint}
    (hbound : ∀ r ∈ Icc (0 : ℝ) R, |mixedDerivative (a + 6) b F (r, p.2)| ≤ M)
    (hp : p.1 ∈ Icc (0 : ℝ) R) :
    |mixedDerivative a b (radialTwoEndpointCubicQuotient F R) p| ≤ M / 36 := by
  obtain ⟨h0, h1, h2⟩ := radialBoundaryPartials_of_sliceJets hF 0 hleft
  let G : PolarPoint → ℝ := reflectRadialField R (radialCubicQuotient F)
  have hG : ContDiff ℝ ∞ G :=
    contDiff_reflectRadialField R (contDiff_radialCubicQuotient hF h0 h1 h2)
  obtain ⟨hG0, hG1, hG2⟩ := radialBoundaryPartials_of_sliceJets hG 0
    (reflectedRadialCubicQuotient_zero_jets hF hR hleft hright)
  have hGbound : ∀ r ∈ Icc (0 : ℝ) R,
      |mixedDerivative (a + 3) b G (r, p.2)| ≤ M / 6 := by
    intro r hr
    change |mixedDerivative (a + 3) b
      (reflectRadialField R (radialCubicQuotient F)) (r, p.2)| ≤ M / 6
    rw [abs_mixedDerivative_reflectRadialField]
    apply abs_mixedDerivative_radialCubicQuotient_le_sixth hF h0 h1 h2 (a + 3) b
    · intro t ht
      simpa only [Nat.add_assoc] using hbound t ht
    · exact ⟨sub_nonneg.mpr hr.2, sub_le_self _ hr.1⟩
  change |mixedDerivative a b (reflectRadialField R (radialCubicQuotient G)) p| ≤ M / 36
  rw [abs_mixedDerivative_reflectRadialField]
  calc
    |mixedDerivative a b (radialCubicQuotient G) (R - p.1, p.2)| ≤ (M / 6) / 6 :=
      abs_mixedDerivative_radialCubicQuotient_le_sixth hG hG0 hG1 hG2 a b hGbound
        ⟨sub_nonneg.mpr hp.2, sub_le_self _ hp.1⟩
    _ = M / 36 := by ring

def translateRadialField (l : ℝ) (F : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  F (l + p.1, p.2)

theorem mixedDerivative_translateRadialField (l : ℝ) (F : PolarPoint → ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (translateRadialField l F) p =
      mixedDerivative a b F (l + p.1, p.2) := by
  simpa only [mixedDerivative, translateRadialField] using
    congrFun (iteratedDeriv_comp_const_add a
      (fun r : ℝ => iteratedDeriv b (fun θ : ℝ => F (r, θ)) p.2) l) p.1

/-- The actual cylindrical quotient for arbitrary ordered radial endpoints. -/
def intervalRadialCubicQuotient (F : PolarPoint → ℝ) (l r : ℝ) : PolarPoint → ℝ :=
  translateRadialField (-l)
    (radialTwoEndpointCubicQuotient (translateRadialField l F) (r - l))

theorem intervalRadialCubicQuotient_eq_div (F : PolarPoint → ℝ)
    {l r : ℝ} {p : PolarPoint} (hp : p.1 ∈ Ioo l r) :
    intervalRadialCubicQuotient F l r p = F p / ((p.1 - l) * (r - p.1)) ^ 3 := by
  have hvalue : intervalRadialCubicQuotient F l r p =
      intervalCubicQuotient (fun x : ℝ => F (x, p.2)) l r p.1 := by
    change twoEndpointCubicQuotient (fun x : ℝ => F (l + x, p.2)) (r - l) (-l + p.1) =
      twoEndpointCubicQuotient (fun x : ℝ => F (l + x, p.2)) (r - l) (p.1 - l)
    congr 1
    ring
  rw [hvalue, intervalCubicQuotient_eq_div _ hp]

/-- The mixed estimate on an arbitrary component, with the same fixed loss
six and uniform constant `1 / 36`. -/
theorem abs_mixedDerivative_intervalRadialCubicQuotient_le
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) {l r : ℝ} (hlr : l < r)
    (hleft : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun x : ℝ => F (x, θ)) l = 0)
    (hright : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun x : ℝ => F (x, θ)) r = 0)
    (a b : ℕ) {M : ℝ} {p : PolarPoint}
    (hbound : ∀ x ∈ Icc l r, |mixedDerivative (a + 6) b F (x, p.2)| ≤ M)
    (hp : p.1 ∈ Icc l r) :
    |mixedDerivative a b (intervalRadialCubicQuotient F l r) p| ≤ M / 36 := by
  let G : PolarPoint → ℝ := translateRadialField l F
  have hG : ContDiff ℝ ∞ G :=
    hF.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
  have hGl : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun x : ℝ => G (x, θ)) 0 = 0 := by
    intro θ i hi
    calc
      iteratedDeriv i (fun x : ℝ => G (x, θ)) 0 =
          iteratedDeriv i (fun x : ℝ => F (x, θ)) (l + 0) :=
        congrFun (iteratedDeriv_comp_const_add i (fun x : ℝ => F (x, θ)) l) 0
      _ = 0 := by simpa only [add_zero] using hleft θ i hi
  have hGr : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun x : ℝ => G (x, θ)) (r - l) = 0 := by
    intro θ i hi
    have hsum : l + (r - l) = r := by ring
    calc
      iteratedDeriv i (fun x : ℝ => G (x, θ)) (r - l) =
          iteratedDeriv i (fun x : ℝ => F (x, θ)) (l + (r - l)) :=
        congrFun (iteratedDeriv_comp_const_add i (fun x : ℝ => F (x, θ)) l) (r - l)
      _ = 0 := by simpa only [hsum] using hright θ i hi
  have hGb : ∀ x ∈ Icc (0 : ℝ) (r - l),
      |mixedDerivative (a + 6) b G (x, p.2)| ≤ M := by
    intro x hx
    change |mixedDerivative (a + 6) b (translateRadialField l F) (x, p.2)| ≤ M
    rw [mixedDerivative_translateRadialField]
    apply hbound (l + x)
    constructor <;> linarith [hx.1, hx.2]
  change |mixedDerivative a b (translateRadialField (-l)
    (radialTwoEndpointCubicQuotient G (r - l))) p| ≤ M / 36
  rw [mixedDerivative_translateRadialField]
  apply abs_mixedDerivative_radialTwoEndpointCubicQuotient_le (p := (-l + p.1, p.2)) hG
    (sub_pos.mpr hlr) hGl hGr a b hGb
  constructor <;> linarith [hp.1, hp.2]

/-- Agreement on a full open radial cylinder determines every mixed jet
at an interior point; no regularity of the first representative is needed. -/
theorem mixedDerivative_eq_of_eqOn_radialCylinder
    {F G : PolarPoint → ℝ} {l r : ℝ}
    (h : ∀ x ∈ Ioo l r, ∀ θ : ℝ, F (x, θ) = G (x, θ))
    (a b : ℕ) {p : PolarPoint} (hp : p.1 ∈ Ioo l r) :
    mixedDerivative a b F p = mixedDerivative a b G p := by
  have heq : (fun x : ℝ => iteratedDeriv b (fun θ : ℝ => F (x, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun x : ℝ => iteratedDeriv b (fun θ : ℝ => G (x, θ)) p.2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with x hx
    have hslice : (fun θ : ℝ => F (x, θ)) = (fun θ : ℝ => G (x, θ)) :=
      funext (h x hx)
    rw [hslice]
  exact (heq.iteratedDeriv a).eq_of_nhds

/-- The bound applies to an actual divided coefficient specified only by
the identity `F = d³ e` on the open component.  Its unconstrained values
outside the component do not affect interior derivatives. -/
theorem abs_mixedDerivative_of_twoEndpointCubicFactorization
    {F e : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) {l r : ℝ} (hlr : l < r)
    (hleft : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun x : ℝ => F (x, θ)) l = 0)
    (hright : ∀ θ : ℝ, ∀ i : ℕ, i ≤ 2 →
      iteratedDeriv i (fun x : ℝ => F (x, θ)) r = 0)
    (hfactor : ∀ q : PolarPoint, q.1 ∈ Ioo l r →
      F q = ((q.1 - l) * (r - q.1)) ^ 3 * e q)
    (a b : ℕ) {M : ℝ} {p : PolarPoint}
    (hbound : ∀ x ∈ Icc l r, |mixedDerivative (a + 6) b F (x, p.2)| ≤ M)
    (hp : p.1 ∈ Ioo l r) : |mixedDerivative a b e p| ≤ M / 36 := by
  have heq : ∀ x ∈ Ioo l r, ∀ θ : ℝ,
      e (x, θ) = intervalRadialCubicQuotient F l r (x, θ) := by
    intro x hx θ
    rw [intervalRadialCubicQuotient_eq_div F hx]
    have hden : ((x - l) * (r - x)) ^ 3 ≠ 0 :=
      pow_ne_zero 3 (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)).ne'
    apply (eq_div_iff hden).mpr
    rw [hfactor (x, θ) hx]
    ring
  rw [mixedDerivative_eq_of_eqOn_radialCylinder heq a b hp]
  exact abs_mixedDerivative_intervalRadialCubicQuotient_le hF hlr hleft hright a b hbound
    ⟨hp.1.le, hp.2.le⟩

end ContinuousFlexibility.Analysis
