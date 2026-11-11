import ContinuousFlexibility.Radial.MorseWeakOperator
import ContinuousFlexibility.Statements.Radial

/-!
# The actual absolute-potential Morse energy domain

The third coordinate is literally `sqrt (1 + |morsePotential j A B|) * u`.
Bounded continuous multipliers identify this graph with the exponential
weak-energy graph for positive `j,A`. Its signed integral form is matched
with the existing Morse form. No regularity of arbitrary L² distributional
solutions, maximal distribution domain, or operator graph core is asserted.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

abbrev MorsePotentialTriple : Type := MorseL2 × MorseL2 × MorseL2

def morseAbsoluteWeight (j A B x : ℝ) : ℝ :=
  sqrt (1 + |Statements.morsePotential j A B x|)

def morseWeightUpperConstant (j A B : ℝ) : ℝ := sqrt (1 + j ^ 2 * A + |j ^ 2 * B|)

def morseWeightLowerConstant (j A B : ℝ) : ℝ :=
  sqrt (2 * (1 + j ^ 2 * A / 2 + |j ^ 2 * B|) / (j ^ 2 * A))

theorem morsePotential_quadratic (j A B x : ℝ) :
    Statements.morsePotential j A B x =
      (j ^ 2 * A) * (exp (-x) ^ 2 - exp (-x)) + j ^ 2 * B := by
  have he : exp (-2 * x) = exp (-x) ^ 2 := by
    rw [show -2 * x = -x + -x by ring, exp_add, pow_two]
  unfold Statements.morsePotential morseRho
  rw [he]
  ring

theorem continuous_morseAbsoluteWeight (j A B : ℝ) :
    Continuous (morseAbsoluteWeight j A B) := by
  unfold morseAbsoluteWeight
  simp_rw [morsePotential_quadratic]
  fun_prop

theorem morseAbsoluteWeight_pos (j A B x : ℝ) : 0 < morseAbsoluteWeight j A B x :=
  sqrt_pos.mpr (by positivity)

theorem morseAbsoluteWeight_sq (j A B x : ℝ) :
    morseAbsoluteWeight j A B x ^ 2 = 1 + |Statements.morsePotential j A B x| :=
  sq_sqrt (by positivity)

theorem morsePotential_lower {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B x : ℝ) :
    j ^ 2 * B - j ^ 2 * A / 4 ≤ Statements.morsePotential j A B x := by
  have ha : 0 ≤ j ^ 2 * A := (mul_pos (sq_pos_of_pos hj) hA).le
  have h := mul_nonneg ha (sq_nonneg (exp (-x) - 1 / 2))
  rw [morsePotential_quadratic]
  nlinarith

theorem morseAbsoluteWeight_controls_exp {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B x : ℝ) :
    exp (-x) ≤ morseWeightLowerConstant j A B * morseAbsoluteWeight j A B x := by
  let a : ℝ := j ^ 2 * A
  let b : ℝ := j ^ 2 * B
  let t : ℝ := exp (-x)
  let v : ℝ := Statements.morsePotential j A B x
  have ha : 0 < a := mul_pos (sq_pos_of_pos hj) hA
  have ht : 0 ≤ t := (exp_pos _).le
  have hv : v = a * (t ^ 2 - t) + b := morsePotential_quadratic j A B x
  have hb : a * t ^ 2 ≤ 2 * |v| + a + 2 * |b| := by
    nlinarith [mul_nonneg ha.le (sq_nonneg (t - 1)), le_abs_self v, neg_le_abs b]
  have hprod : a * t ^ 2 ≤ 2 * (1 + a / 2 + |b|) * (1 + |v|) := by
    nlinarith [mul_nonneg (show 0 ≤ a / 2 + |b| by positivity) (abs_nonneg v)]
  have hk : morseWeightLowerConstant j A B ^ 2 = 2 * (1 + a / 2 + |b|) / a :=
    sq_sqrt (by positivity)
  have hs : t ^ 2 ≤
      (morseWeightLowerConstant j A B * morseAbsoluteWeight j A B x) ^ 2 := by
    rw [mul_pow, hk, morseAbsoluteWeight_sq, div_mul_eq_mul_div]
    exact (le_div_iff₀ ha).mpr (by nlinarith [hprod])
  exact (sq_le_sq₀ ht (mul_nonneg (sqrt_nonneg _)
    (morseAbsoluteWeight_pos j A B x).le)).mp hs

theorem morseAbsoluteWeight_le_exp {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B x : ℝ) :
    morseAbsoluteWeight j A B x ≤ morseWeightUpperConstant j A B * (1 + exp (-x)) := by
  let a : ℝ := j ^ 2 * A
  let b : ℝ := j ^ 2 * B
  let t : ℝ := exp (-x)
  let v : ℝ := Statements.morsePotential j A B x
  have ha : 0 ≤ a := (mul_pos (sq_pos_of_pos hj) hA).le
  have ht : 0 ≤ t := (exp_pos _).le
  have hv : v = a * t ^ 2 - a * t + b := by
    dsimp only [v]
    rw [morsePotential_quadratic]
    dsimp [a, b, t]
    ring
  have hb : |v| ≤ a * t ^ 2 + a * t + |b| := by
    rw [hv]
    calc
      _ ≤ |a * t ^ 2 - a * t| + |b| := abs_add_le _ _
      _ ≤ |a * t ^ 2| + |a * t| + |b| := by linarith [abs_sub (a * t ^ 2) (a * t)]
      _ = a * t ^ 2 + a * t + |b| := by
        rw [abs_of_nonneg (mul_nonneg ha (sq_nonneg t)), abs_of_nonneg (mul_nonneg ha ht)]
  have hk : morseWeightUpperConstant j A B ^ 2 = 1 + a + |b| := sq_sqrt (by positivity)
  have hs : morseAbsoluteWeight j A B x ^ 2 ≤
      (morseWeightUpperConstant j A B * (1 + t)) ^ 2 := by
    rw [morseAbsoluteWeight_sq, mul_pow, hk]
    nlinarith [mul_nonneg (show 0 ≤ 2 + a + 2 * |b| by positivity) ht,
      mul_nonneg (show 0 ≤ 1 + |b| by positivity) (sq_nonneg t)]
  exact (sq_le_sq₀ (morseAbsoluteWeight_pos j A B x).le
    (mul_nonneg (sqrt_nonneg _) (by positivity))).mp hs

def morsePotentialExpCoefficient (j A B x : ℝ) : ℝ := exp (-x) / morseAbsoluteWeight j A B x

def morsePotentialSumCoefficient (j A B x : ℝ) : ℝ :=
  morseAbsoluteWeight j A B x / (1 + exp (-x))

theorem continuous_morsePotentialExpCoefficient (j A B : ℝ) :
    Continuous (morsePotentialExpCoefficient j A B) :=
  continuous_id.neg.rexp.div (continuous_morseAbsoluteWeight j A B)
    (fun x => (morseAbsoluteWeight_pos j A B x).ne')

theorem continuous_morsePotentialSumCoefficient (j A B : ℝ) :
    Continuous (morsePotentialSumCoefficient j A B) :=
  (continuous_morseAbsoluteWeight j A B).div (continuous_const.add continuous_id.neg.rexp)
    (fun x => by positivity)

theorem morsePotentialExpCoefficient_bound {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B x : ℝ) : |morsePotentialExpCoefficient j A B x| ≤ morseWeightLowerConstant j A B := by
  rw [morsePotentialExpCoefficient, abs_div, abs_of_pos (exp_pos _),
    abs_of_pos (morseAbsoluteWeight_pos j A B x)]
  exact (div_le_iff₀ (morseAbsoluteWeight_pos j A B x)).mpr
    (morseAbsoluteWeight_controls_exp hj hA B x)

theorem morsePotentialSumCoefficient_bound {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B x : ℝ) : |morsePotentialSumCoefficient j A B x| ≤ morseWeightUpperConstant j A B := by
  rw [morsePotentialSumCoefficient, abs_div, abs_of_pos (morseAbsoluteWeight_pos j A B x),
    abs_of_pos (by positivity : (0 : ℝ) < 1 + exp (-x))]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + exp (-x))).mpr
    (morseAbsoluteWeight_le_exp hj hA B x)

def morsePotentialExpMultiplier {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    MorseL2 →L[ℝ] MorseL2 :=
  morseL2Multiplier _ (continuous_morsePotentialExpCoefficient j A B)
    (morseWeightLowerConstant j A B) (morsePotentialExpCoefficient_bound hj hA B)

def morsePotentialSumMultiplier {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    MorseL2 →L[ℝ] MorseL2 :=
  morseL2Multiplier _ (continuous_morsePotentialSumCoefficient j A B)
    (morseWeightUpperConstant j A B) (morsePotentialSumCoefficient_bound hj hA B)

theorem morsePotentialExpMultiplier_ae {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (u : MorseL2) :
    (morsePotentialExpMultiplier hj hA B u : ℝ → ℝ) =ᵐ[volume]
      (fun x => morsePotentialExpCoefficient j A B x * u x) :=
  morseL2Mul_coeFn _ (continuous_morsePotentialExpCoefficient j A B)
    (morseWeightLowerConstant j A B) (morsePotentialExpCoefficient_bound hj hA B) u

theorem morsePotentialSumMultiplier_ae {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (u : MorseL2) :
    (morsePotentialSumMultiplier hj hA B u : ℝ → ℝ) =ᵐ[volume]
      (fun x => morsePotentialSumCoefficient j A B x * u x) :=
  morseL2Mul_coeFn _ (continuous_morsePotentialSumCoefficient j A B)
    (morseWeightUpperConstant j A B) (morsePotentialSumCoefficient_bound hj hA B) u

theorem morsePotentialExpCoefficient_mul (j A B x : ℝ) :
    morsePotentialExpCoefficient j A B x * morseAbsoluteWeight j A B x = exp (-x) :=
  div_mul_cancel₀ _ (morseAbsoluteWeight_pos j A B x).ne'

theorem morsePotentialSumCoefficient_mul (j A B x : ℝ) :
    morsePotentialSumCoefficient j A B x * (1 + exp (-x)) = morseAbsoluteWeight j A B x :=
  div_mul_cancel₀ _ (by positivity)

theorem morsePotential_memLp_iff_exp {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (fun x => morseAbsoluteWeight j A B x * f x) 2 volume ↔
      MemLp (fun x => exp (-x) * f x) 2 volume := by
  constructor
  · intro hm
    have h := morseMemLp_bounded_mul (continuous_morsePotentialExpCoefficient j A B)
      (morsePotentialExpCoefficient_bound hj hA B) hm
    simpa only [← mul_assoc, morsePotentialExpCoefficient_mul] using h
  · intro he
    have h := morseMemLp_bounded_mul (continuous_morsePotentialSumCoefficient j A B)
      (morsePotentialSumCoefficient_bound hj hA B) (hf.add he)
    convert h using 1
    funext x
    simp only [Pi.add_apply]
    rw [show morsePotentialSumCoefficient j A B x * (f x + exp (-x) * f x) =
      (morsePotentialSumCoefficient j A B x * (1 + exp (-x))) * f x by ring,
      morsePotentialSumCoefficient_mul]

theorem morseWeakDerivative_iff_public (u d : MorseL2) :
    MorseWeakDerivativeL2 u d ↔ Statements.WeakRadialDerivative u d := by
  constructor <;> intro h φ hφ hc <;> have hh := h φ hφ hc <;> linarith

/-- An independently specified weak-derivative and absolute-potential graph. -/
def morsePotentialEnergyGraph (j A B : ℝ) : Submodule ℝ MorsePotentialTriple where
  carrier := {p | MorseWeakDerivativeL2 p.1 p.2.1 ∧
    (p.2.2 : ℝ → ℝ) =ᵐ[volume] (fun x => morseAbsoluteWeight j A B x * p.1 x)}
  zero_mem' := by
    refine ⟨morseWeakDerivativeL2_zero, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
    change (0 : MorseL2) x = morseAbsoluteWeight j A B x * (0 : MorseL2) x
    rw [hx]
    simp
  add_mem' := by
    intro p q hp hq
    refine ⟨hp.1.add hq.1, ?_⟩
    filter_upwards [hp.2, hq.2, Lp.coeFn_add p.2.2 q.2.2,
      Lp.coeFn_add p.1 q.1] with x hx hy h2 h0
    change (p.2.2 + q.2.2) x = morseAbsoluteWeight j A B x * (p.1 + q.1) x
    rw [h2, h0]
    simp only [Pi.add_apply]
    rw [hx, hy]
    ring
  smul_mem' := by
    intro c p hp
    refine ⟨hp.1.smul c, ?_⟩
    filter_upwards [hp.2, Lp.coeFn_smul c p.2.2, Lp.coeFn_smul c p.1] with x hx h2 h0
    change (c • p.2.2) x = morseAbsoluteWeight j A B x * (c • p.1) x
    rw [h2, h0]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx]
    ring

theorem morsePotentialEnergyGraph_eq_public (j A B : ℝ) :
    (morsePotentialEnergyGraph j A B : Set MorsePotentialTriple) =
      Statements.SchrodingerEnergyLift (Statements.morsePotential j A B) := by
  ext p
  exact and_congr (morseWeakDerivative_iff_public p.1 p.2.1) Iff.rfl

private def morsePotentialProj0 : MorsePotentialTriple →L[ℝ] MorseL2 :=
  ContinuousLinearMap.fst ℝ MorseL2 (MorseL2 × MorseL2)

private def morsePotentialProj1 : MorsePotentialTriple →L[ℝ] MorseL2 :=
  (ContinuousLinearMap.fst ℝ MorseL2 MorseL2).comp
    (ContinuousLinearMap.snd ℝ MorseL2 (MorseL2 × MorseL2))

private def morsePotentialProj2 : MorsePotentialTriple →L[ℝ] MorseL2 :=
  (ContinuousLinearMap.snd ℝ MorseL2 MorseL2).comp
    (ContinuousLinearMap.snd ℝ MorseL2 (MorseL2 × MorseL2))

private def morseExpProj (i : Fin 3) : MorseEnergyTriple →L[ℝ] MorseL2 :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => MorseL2) i

def morsePotentialToExp {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    MorsePotentialTriple →L[ℝ] MorseEnergyTriple :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => MorseL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![morsePotentialProj0, morsePotentialProj1,
      (morsePotentialExpMultiplier hj hA B).comp morsePotentialProj2])

def morseExpToPotential {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    MorseEnergyTriple →L[ℝ] MorsePotentialTriple :=
  (morseExpProj 0).prod ((morseExpProj 1).prod
    (((morsePotentialSumMultiplier hj hA B).comp (morseExpProj 0)) +
      ((morsePotentialSumMultiplier hj hA B).comp (morseExpProj 2))))

@[simp] theorem morsePotentialToExp_zero {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (p : MorsePotentialTriple) : morsePotentialToExp hj hA B p 0 = p.1 := rfl

@[simp] theorem morsePotentialToExp_one {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (p : MorsePotentialTriple) : morsePotentialToExp hj hA B p 1 = p.2.1 := rfl

@[simp] theorem morsePotentialToExp_two {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (p : MorsePotentialTriple) :
    morsePotentialToExp hj hA B p 2 = morsePotentialExpMultiplier hj hA B p.2.2 := rfl

@[simp] theorem morseExpToPotential_base {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (p : MorseEnergyTriple) : (morseExpToPotential hj hA B p).1 = p 0 := rfl

@[simp] theorem morseExpToPotential_derivative {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (p : MorseEnergyTriple) : (morseExpToPotential hj hA B p).2.1 = p 1 := rfl

@[simp] theorem morseExpToPotential_weight {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) (p : MorseEnergyTriple) :
    (morseExpToPotential hj hA B p).2.2 =
      morsePotentialSumMultiplier hj hA B (p 0) + morsePotentialSumMultiplier hj hA B (p 2) := rfl

theorem morsePotentialToExp_mem {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ)
    {p : MorsePotentialTriple} (hp : p ∈ morsePotentialEnergyGraph j A B) :
    morsePotentialToExp hj hA B p ∈ morseEnergyGraph := by
  apply (mem_morseEnergyGraph_iff _).mpr
  refine ⟨hp.1, ?_⟩
  filter_upwards [hp.2, morsePotentialExpMultiplier_ae hj hA B p.2.2] with x hx hr
  change morsePotentialExpMultiplier hj hA B p.2.2 x = exp (-x) * p.1 x
  rw [hr, hx, ← mul_assoc, morsePotentialExpCoefficient_mul]

theorem morseExpToPotential_mem {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ)
    {p : MorseEnergyTriple} (hp : p ∈ morseEnergyGraph) :
    morseExpToPotential hj hA B p ∈ morsePotentialEnergyGraph j A B := by
  have hw := (mem_morseEnergyGraph_iff _).mp hp
  refine ⟨hw.1, ?_⟩
  filter_upwards [hw.2, morsePotentialSumMultiplier_ae hj hA B (p 0),
    morsePotentialSumMultiplier_ae hj hA B (p 2),
    Lp.coeFn_add (morsePotentialSumMultiplier hj hA B (p 0))
      (morsePotentialSumMultiplier hj hA B (p 2))] with x hx h0 h2 ha
  change (morsePotentialSumMultiplier hj hA B (p 0) +
    morsePotentialSumMultiplier hj hA B (p 2)) x = morseAbsoluteWeight j A B x * p 0 x
  rw [ha]
  simp only [Pi.add_apply]
  rw [h0, h2, hx]
  calc
    _ = (morsePotentialSumCoefficient j A B x * (1 + exp (-x))) * p 0 x := by ring
    _ = _ := by rw [morsePotentialSumCoefficient_mul]

theorem morseExpToPotential_toExp {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ)
    {p : MorsePotentialTriple} (hp : p ∈ morsePotentialEnergyGraph j A B) :
    morseExpToPotential hj hA B (morsePotentialToExp hj hA B p) = p := by
  have hh := (morseExpToPotential_mem hj hA B (morsePotentialToExp_mem hj hA B hp)).2
  refine Prod.ext rfl (Prod.ext rfl ?_)
  apply Lp.ext
  filter_upwards [hh, hp.2] with x hx hy
  change (morseExpToPotential hj hA B (morsePotentialToExp hj hA B p)).2.2 x =
    morseAbsoluteWeight j A B x * p.1 x at hx
  exact hx.trans hy.symm

theorem morsePotentialToExp_toPotential {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ)
    {p : MorseEnergyTriple} (hp : p ∈ morseEnergyGraph) :
    morsePotentialToExp hj hA B (morseExpToPotential hj hA B p) = p := by
  have hh := (mem_morseEnergyGraph_iff _).mp
    (morsePotentialToExp_mem hj hA B (morseExpToPotential_mem hj hA B hp))
  have hw := (mem_morseEnergyGraph_iff _).mp hp
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · rfl
  · apply Lp.ext
    filter_upwards [hh.2, hw.2] with x hx hy
    change morsePotentialToExp hj hA B (morseExpToPotential hj hA B p) 2 x = p 2 x
    change morsePotentialToExp hj hA B (morseExpToPotential hj hA B p) 2 x =
      exp (-x) * p 0 x at hx
    exact hx.trans hy.symm

theorem morsePotentialEnergyGraph_isClosed {j A : ℝ}
    (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    IsClosed (morsePotentialEnergyGraph j A B : Set MorsePotentialTriple) := by
  have heq : (morsePotentialEnergyGraph j A B : Set MorsePotentialTriple) =
      {p | morsePotentialToExp hj hA B p ∈ morseEnergyGraph} ∩
      {p | morseExpToPotential hj hA B (morsePotentialToExp hj hA B p) = p} := by
    ext p
    constructor
    · intro hp
      exact ⟨morsePotentialToExp_mem hj hA B hp, morseExpToPotential_toExp hj hA B hp⟩
    · rintro ⟨hp, he⟩
      have h := morseExpToPotential_mem hj hA B hp
      rwa [he] at h
  rw [heq]
  exact (morseEnergyGraph_isClosed.preimage (morsePotentialToExp hj hA B).continuous).inter
    (isClosed_eq ((morseExpToPotential hj hA B).continuous.comp
      (morsePotentialToExp hj hA B).continuous) continuous_id)

abbrev MorsePotentialEnergySpace (j A B : ℝ) := morsePotentialEnergyGraph j A B

theorem morsePotentialEnergySpace_completeSpace {j A : ℝ}
    (hj : 0 < j) (hA : 0 < A) (B : ℝ) : CompleteSpace (MorsePotentialEnergySpace j A B) :=
  (morsePotentialEnergyGraph_isClosed hj hA B).isComplete.completeSpace_coe

def morsePotentialEnergyToExp {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    MorsePotentialEnergySpace j A B →L[ℝ] MorseWeakEnergy :=
  ((morsePotentialToExp hj hA B).comp (morsePotentialEnergyGraph j A B).subtypeL).codRestrict
    morseEnergyGraph (fun p => morsePotentialToExp_mem hj hA B p.property)

def morseExpEnergyToPotential {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    MorseWeakEnergy →L[ℝ] MorsePotentialEnergySpace j A B :=
  ((morseExpToPotential hj hA B).comp morseEnergyGraph.subtypeL).codRestrict
    (morsePotentialEnergyGraph j A B) (fun p => morseExpToPotential_mem hj hA B p.property)

def morsePotentialEnergyEquiv {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    MorsePotentialEnergySpace j A B ≃L[ℝ] MorseWeakEnergy :=
  ContinuousLinearEquiv.equivOfInverse (morsePotentialEnergyToExp hj hA B)
    (morseExpEnergyToPotential hj hA B)
    (fun p => Subtype.ext (morseExpToPotential_toExp hj hA B p.property))
    (fun p => Subtype.ext (morsePotentialToExp_toPotential hj hA B p.property))

theorem morsePublicEnergyLift_isClosed {j A : ℝ}
    (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    IsClosed (Statements.SchrodingerEnergyLift (Statements.morsePotential j A B)) := by
  rw [← morsePotentialEnergyGraph_eq_public]
  exact morsePotentialEnergyGraph_isClosed hj hA B

theorem morseExpToPotential_compact_lift {j A : ℝ} (hj : 0 < j) (hA : 0 < A)
    (B : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    morseExpToPotential hj hA B (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)).val ∈
      Statements.SchrodingerEnergyCore (Statements.morsePotential j A B) := by
  let U := morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)
  have hb : (morseEnergyBase U : ℝ → ℝ) =ᵐ[volume] φ := by
    change (morseEnergyBase (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)) : ℝ → ℝ)
      =ᵐ[volume] φ
    rw [morseEnergyLift_base]
    exact MemLp.coeFn_toLp _
  have hd : (morseEnergyDerivative U : ℝ → ℝ) =ᵐ[volume] deriv φ := by
    change (morseEnergyDerivative (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)) : ℝ → ℝ)
      =ᵐ[volume] deriv φ
    rw [morseEnergyLift_derivative]
    exact MemLp.coeFn_toLp _
  refine ⟨φ, hφ, hc, hb, hd, ?_⟩
  have hw := (morseExpToPotential_mem hj hA B U.property).2
  filter_upwards [hw, hb] with x hx hbase
  change (morseExpToPotential hj hA B U.val).2.2 x = morseAbsoluteWeight j A B x * φ x
  change (morseExpToPotential hj hA B U.val).2.2 x =
    morseAbsoluteWeight j A B x * morseEnergyBase U x at hx
  rw [hx, hbase]

theorem morsePublicEnergyCore_subset (j A B : ℝ) :
    Statements.SchrodingerEnergyCore (Statements.morsePotential j A B) ⊆
      Statements.SchrodingerEnergyLift (Statements.morsePotential j A B) := by
  rintro p ⟨φ, hφ, hc, hb, hd, hw⟩
  let ht := compactSmooth_morseEnergyDomain hφ hc
  have h0 : p.1 = ht.2.1.toLp φ := Lp.ext (hb.trans (MemLp.coeFn_toLp _).symm)
  have h1 : p.2.1 = ht.2.2.1.toLp (deriv φ) := Lp.ext (hd.trans (MemLp.coeFn_toLp _).symm)
  refine ⟨?_, ?_⟩
  · apply (morseWeakDerivative_iff_public _ _).mp
    rw [h0, h1]
    exact morseWeakDerivativeL2_of_energyDomain ht
  · filter_upwards [hw, hb] with x hx hbase
    change p.2.2 x = morseAbsoluteWeight j A B x * p.1 x
    rw [hx, hbase]
    rfl

/-- The closure is in the exact product topology used by the public
absolute-potential energy contract. The weighted coordinate need not be smooth. -/
theorem morsePublicEnergyCore_closure {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    closure (Statements.SchrodingerEnergyCore (Statements.morsePotential j A B)) =
      Statements.SchrodingerEnergyLift (Statements.morsePotential j A B) := by
  apply le_antisymm
  · exact closure_minimal (morsePublicEnergyCore_subset j A B) (morsePublicEnergyLift_isClosed hj hA B)
  · intro p hp
    have hown : p ∈ morsePotentialEnergyGraph j A B := by
      change p ∈ (morsePotentialEnergyGraph j A B : Set MorsePotentialTriple)
      rwa [morsePotentialEnergyGraph_eq_public]
    let U : MorseWeakEnergy := morsePotentialEnergyToExp hj hA B ⟨p, hown⟩
    let F : MorseWeakEnergy → MorsePotentialTriple := fun W => morseExpToPotential hj hA B W.val
    have hF : Continuous F :=
      (morseExpToPotential hj hA B).continuous.comp morseEnergyGraph.subtypeL.continuous
    let S : Set MorseWeakEnergy := {W | ∃ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hcφ : HasCompactSupport φ),
      W = morseEnergyLift (compactSmooth_morseEnergyDomain hφ hcφ)}
    have hU : U ∈ closure S := morseCompactSmoothEnergy_dense U
    have him : F '' S ⊆ Statements.SchrodingerEnergyCore (Statements.morsePotential j A B) := by
      rintro _ ⟨W, ⟨φ, hφ, hc, rfl⟩, rfl⟩
      exact morseExpToPotential_compact_lift hj hA B hφ hc
    have hsub := (image_closure_subset_closure_image hF).trans (closure_mono him)
    have hpcl := hsub ⟨U, hU, rfl⟩
    have heq : F U = p := morseExpToPotential_toExp hj hA B hown
    rwa [heq] at hpcl

private theorem morseL2_inner_integral (u v : MorseL2) :
    ⟪u, v⟫_ℝ = ∫ x : ℝ, u x * v x := by
  rw [L2.inner_def]
  congr 1
  funext x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem morsePotential_pairing_ae (j A B : ℝ) (U W : MorseWeakEnergy) :
    (fun x => Statements.morsePotential j A B x * morseEnergyBase U x * morseEnergyBase W x) =ᵐ[volume]
      (fun x => (j ^ 2 * A) * (morseEnergyWeight U x * morseEnergyWeight W x) -
        (j ^ 2 * A) * (morseEnergyWeight U x * morseEnergyBase W x) +
        (j ^ 2 * B) * (morseEnergyBase U x * morseEnergyBase W x)) := by
  filter_upwards [morseEnergyWeight_ae U, morseEnergyWeight_ae W] with x hu hw
  rw [hu, hw, morsePotential_quadratic]
  ring

theorem morsePotential_pairing_integrable (j A B : ℝ) (U W : MorseWeakEnergy) :
    Integrable (fun x => Statements.morsePotential j A B x *
      morseEnergyBase U x * morseEnergyBase W x) volume := by
  have hWW : Integrable (fun x => morseEnergyWeight U x * morseEnergyWeight W x) volume :=
    (Lp.memLp (morseEnergyWeight U)).integrable_mul (Lp.memLp (morseEnergyWeight W))
  have hWU : Integrable (fun x => morseEnergyWeight U x * morseEnergyBase W x) volume :=
    (Lp.memLp (morseEnergyWeight U)).integrable_mul (Lp.memLp (morseEnergyBase W))
  have hUU : Integrable (fun x => morseEnergyBase U x * morseEnergyBase W x) volume :=
    (Lp.memLp (morseEnergyBase U)).integrable_mul (Lp.memLp (morseEnergyBase W))
  exact (((hWW.const_mul (j ^ 2 * A)).sub (hWU.const_mul (j ^ 2 * A))).add
    (hUU.const_mul (j ^ 2 * B))).congr (morsePotential_pairing_ae j A B U W).symm

theorem morsePotential_pairing_integral (j A B : ℝ) (U W : MorseWeakEnergy) :
    (∫ x : ℝ, Statements.morsePotential j A B x * morseEnergyBase U x * morseEnergyBase W x) =
      (j ^ 2 * A) * ⟪morseEnergyWeight U, morseEnergyWeight W⟫_ℝ -
        (j ^ 2 * A) * ⟪morseEnergyWeight U, morseEnergyBase W⟫_ℝ +
        (j ^ 2 * B) * ⟪morseEnergyBase U, morseEnergyBase W⟫_ℝ := by
  have hWW : Integrable (fun x => morseEnergyWeight U x * morseEnergyWeight W x) volume :=
    (Lp.memLp (morseEnergyWeight U)).integrable_mul (Lp.memLp (morseEnergyWeight W))
  have hWU : Integrable (fun x => morseEnergyWeight U x * morseEnergyBase W x) volume :=
    (Lp.memLp (morseEnergyWeight U)).integrable_mul (Lp.memLp (morseEnergyBase W))
  have hUU : Integrable (fun x => morseEnergyBase U x * morseEnergyBase W x) volume :=
    (Lp.memLp (morseEnergyBase U)).integrable_mul (Lp.memLp (morseEnergyBase W))
  have hadd := integral_add ((hWW.const_mul (j ^ 2 * A)).sub (hWU.const_mul (j ^ 2 * A)))
    (hUU.const_mul (j ^ 2 * B))
  have hsub := integral_sub (hWW.const_mul (j ^ 2 * A)) (hWU.const_mul (j ^ 2 * A))
  simp only [Pi.sub_apply] at hadd hsub
  rw [integral_congr_ae (morsePotential_pairing_ae j A B U W), hadd, hsub]
  simp only [integral_const_mul, ← morseL2_inner_integral]

/-- This is the actual signed-potential integral, with the paper's exact
`α=(j√A-1)/2`, `ω=j√A`, and constant `j²B`. -/
theorem morsePhysicalForm_eq_potential_integral {A : ℝ} (hA : 0 < A)
    (j B : ℝ) (U W : MorseWeakEnergy) :
    morsePhysicalForm ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) U W =
      ⟪morseEnergyDerivative U, morseEnergyDerivative W⟫_ℝ +
        ∫ x : ℝ, Statements.morsePotential j A B x * morseEnergyBase U x * morseEnergyBase W x := by
  have hw : (j * sqrt A) ^ 2 = j ^ 2 * A := by rw [mul_pow, sq_sqrt hA.le]
  have hc : j * sqrt A * (2 * ((j * sqrt A - 1) / 2) + 1) = j ^ 2 * A := by
    calc
      _ = (j * sqrt A) ^ 2 := by ring
      _ = _ := hw
  rw [morsePhysicalForm_apply, morsePotential_pairing_integral, hw, hc]
  ring

/-- Identification with the independently defined public integral form graph. -/
theorem morsePublicFormGraph_iff_associated {j A : ℝ}
    (hj : 0 < j) (hA : 0 < A) (B : ℝ) (u f : MorseL2) :
    Statements.SchrodingerFormGraph (Statements.morsePotential j A B) u f ↔
      (u, f) ∈ morseAssociatedGraph ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) := by
  constructor
  · rintro ⟨d, z, hp, hpair⟩
    have hown : (u, d, z) ∈ morsePotentialEnergyGraph j A B := by
      change (u, d, z) ∈ (morsePotentialEnergyGraph j A B : Set MorsePotentialTriple)
      rwa [morsePotentialEnergyGraph_eq_public]
    let U : MorseWeakEnergy := morsePotentialEnergyToExp hj hA B ⟨(u, d, z), hown⟩
    refine ⟨U, rfl, ?_⟩
    intro W
    have hPW : morseExpToPotential hj hA B W.val ∈
        Statements.SchrodingerEnergyLift (Statements.morsePotential j A B) := by
      rw [← morsePotentialEnergyGraph_eq_public]
      exact morseExpToPotential_mem hj hA B W.property
    have hh := (hpair (morseExpToPotential hj hA B W.val) hPW).2
    change ⟪f, morseEnergyBase W⟫_ℝ = ⟪d, morseEnergyDerivative W⟫_ℝ +
      ∫ x : ℝ, Statements.morsePotential j A B x * u x * morseEnergyBase W x at hh
    rw [morsePhysicalForm_eq_potential_integral hA]
    change ⟪d, morseEnergyDerivative W⟫_ℝ +
      (∫ x : ℝ, Statements.morsePotential j A B x * u x * morseEnergyBase W x) =
        ⟪f, morseEnergyBase W⟫_ℝ
    exact hh.symm
  · rintro ⟨U, rfl, hpair⟩
    let p : MorsePotentialTriple := morseExpToPotential hj hA B U.val
    have hp : p ∈ Statements.SchrodingerEnergyLift (Statements.morsePotential j A B) := by
      rw [← morsePotentialEnergyGraph_eq_public]
      exact morseExpToPotential_mem hj hA B U.property
    refine ⟨p.2.1, p.2.2, hp, ?_⟩
    intro q hq
    have hown : q ∈ morsePotentialEnergyGraph j A B := by
      change q ∈ (morsePotentialEnergyGraph j A B : Set MorsePotentialTriple)
      rwa [morsePotentialEnergyGraph_eq_public]
    let W : MorseWeakEnergy := morsePotentialEnergyToExp hj hA B ⟨q, hown⟩
    refine ⟨?_, ?_⟩
    · change Integrable (fun x => Statements.morsePotential j A B x *
        morseEnergyBase U x * morseEnergyBase W x) volume
      exact morsePotential_pairing_integrable j A B U W
    · have hh := hpair W
      rw [morsePhysicalForm_eq_potential_integral hA] at hh
      change ⟪f, morseEnergyBase W⟫_ℝ =
        ⟪morseEnergyDerivative U, morseEnergyDerivative W⟫_ℝ +
          ∫ x : ℝ, Statements.morsePotential j A B x * morseEnergyBase U x * morseEnergyBase W x
      exact hh.symm

theorem morsePublicWeakGraph_iff_compactWeak {A : ℝ} (hA : 0 < A)
    (j B : ℝ) (u f : MorseL2) :
    Statements.WeakSchrodingerGraph (Statements.morsePotential j A B) u f ↔
      MorseCompactWeakEquation ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) u f := by
  have he : ∀ (φ : ℝ → ℝ) (x : ℝ),
      -deriv (deriv φ) x + Statements.morsePotential j A B x * φ x =
        morseExpression ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) φ x := by
    intro φ x
    rw [← morseSchrodingerExpression_eq hA.le j B φ x]
    unfold morseSchrodingerExpression Statements.morsePotential
    ring
  constructor <;> intro h φ hφ hc <;> simpa only [he] using h φ hφ hc

/-- The weak/form equivalence is asserted for an actual energy lift;
no energy regularity theorem for arbitrary L² weak solutions is assumed. -/
theorem morsePublicWeakGraph_iff_formGraph_of_energy {j A : ℝ}
    (hj : 0 < j) (hA : 0 < A) (B : ℝ) (U : MorseWeakEnergy) (f : MorseL2) :
    Statements.WeakSchrodingerGraph (Statements.morsePotential j A B) (morseEnergyBase U) f ↔
      Statements.SchrodingerFormGraph (Statements.morsePotential j A B) (morseEnergyBase U) f :=
  (morsePublicWeakGraph_iff_compactWeak hA j B (morseEnergyBase U) f).trans
    ((morseAssociatedGraph_iff_compactWeak_of_energy _ _ _ U f).symm.trans
      (morsePublicFormGraph_iff_associated hj hA B (morseEnergyBase U) f).symm)

end ContinuousFlexibility.Radial
