import ContinuousFlexibility.Analysis.N01cDistributedRadialProducts
import ContinuousFlexibility.Analysis.N01cStateParameterJets
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact square-root jets and endpoint cancellation

All derivatives below are actual ordinary or projective derivatives.
An affine optical square has an explicit parameter tower. For spatial
composition, the ordered partitions keep their actual derivative orders.
If every inner jet gains one endpoint distance, the square-root factor
loses precisely one such distance per input and leaves a half power.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual falling coefficient in an ordinary real-power jet. -/
def rpowJetCoefficient (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => rpowJetCoefficient α n * (α - (n : ℝ))

theorem iteratedDeriv_rpow_eq (α : ℝ) (n : ℕ) :
    iteratedDeriv n (fun q : ℝ => q ^ α) =
      fun q => rpowJetCoefficient α n * q ^ (α - (n : ℝ)) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, rpowJetCoefficient, Nat.cast_zero, sub_zero, one_mul]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext q
      rw [deriv_const_mul_field, Real.deriv_rpow_const]
      simp only [rpowJetCoefficient, Nat.cast_add_one]
      rw [show α - (n : ℝ) - 1 = α - ((n : ℝ) + 1) by ring]
      ring

theorem iteratedDeriv_sqrt_eq (n : ℕ) (q : ℝ) :
    iteratedDeriv n Real.sqrt q =
      rpowJetCoefficient (1 / 2) n * q ^ ((1 / 2 : ℝ) - (n : ℝ)) := by
  have hs : Real.sqrt = (fun q : ℝ => q ^ (1 / 2 : ℝ)) :=
    funext Real.sqrt_eq_rpow
  rw [hs, iteratedDeriv_rpow_eq]

section AffineParameterJets

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

def affineRpowJets (α q₀ : ℝ) (L : E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    E [×n]→L[ℝ] ℝ :=
  (rpowJetCoefficient α n * (q₀ + L x) ^ (α - (n : ℝ))) •
    scalarFunctionalProduct L n

theorem affineRpowJets_apply (α q₀ : ℝ) (L : E →L[ℝ] ℝ)
    (n : ℕ) (x : E) (v : Fin n → E) :
    affineRpowJets α q₀ L n x v =
      rpowJetCoefficient α n * (q₀ + L x) ^ (α - (n : ℝ)) *
        ∏ i, L (v i) := by
  simp only [affineRpowJets, smul_apply, smul_eq_mul, scalarFunctionalProduct_apply]

private theorem affineRpowJets_hasLineDerivAt
    (α q₀ : ℝ) (L : E →L[ℝ] ℝ) (n : ℕ) (x : E)
    (hx : 0 < q₀ + L x) (v : Fin n → E) (w : E) :
    HasProjectiveLineDerivAt (fun y : E => affineRpowJets α q₀ L n y v)
      (affineRpowJets α q₀ L (n + 1) x (Fin.cons w v)) x w := by
  have hline : HasDerivAt (fun t : ℝ => (q₀ + L x) + t * L w)
      (L w) (0 : ℝ) := by
    simpa only [one_mul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (L w)).const_add (q₀ + L x)
  have hne : (q₀ + L x) + (0 : ℝ) * L w ≠ 0 := by
    simpa only [zero_mul, add_zero] using hx.ne'
  have hcurve := ((hline.rpow_const (p := α - (n : ℝ)) (Or.inl hne)).const_mul
    (rpowJetCoefficient α n)).mul_const (∏ i, L (v i))
  have hvalue :
      (rpowJetCoefficient α n *
          (L w * (α - (n : ℝ)) *
            ((q₀ + L x) + (0 : ℝ) * L w) ^ (α - (n : ℝ) - 1))) *
          ∏ i, L (v i) =
        affineRpowJets α q₀ L (n + 1) x (Fin.cons w v) := by
    rw [affineRpowJets_apply, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, zero_mul, add_zero,
      rpowJetCoefficient, Nat.cast_add_one]
    rw [show α - (n : ℝ) - 1 = α - ((n : ℝ) + 1) by ring]
    ring
  rw [hvalue] at hcurve
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    affineRpowJets_apply, map_add, map_smul, smul_eq_mul, add_assoc] using
    hcurve.tendsto_slope_zero

/-- Positivity on one fixed open set gives the entire actual affine
real-power tower. No order-dependent neighbourhood is selected. -/
def smoothDirections_affineRpow (α q₀ : ℝ) (L : E →L[ℝ] ℝ)
    {U : Set E} (hU : IsOpen U) (hpos : ∀ x ∈ U, 0 < q₀ + L x) :
    SmoothDirections U (fun x : E => (q₀ + L x) ^ α) where
  open_domain := hU
  D := affineRpowJets α q₀ L
  zero := by
    intro x _
    simp only [affineRpowJets_apply, rpowJetCoefficient, Nat.cast_zero, sub_zero,
      one_mul, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  continuous := by
    intro n
    simp only [affineRpowJets, smul_apply, smul_eq_mul]
    have hq : Continuous (fun z : E × (Fin n → E) => q₀ + L z.1) :=
      continuous_const.add (L.continuous.comp continuous_fst)
    have hp : ContinuousOn
        (fun z : E × (Fin n → E) => (q₀ + L z.1) ^ (α - (n : ℝ)))
        (U ×ˢ (univ : Set (Fin n → E))) :=
      hq.continuousOn.rpow_const
        (fun z hz => Or.inl (hpos z.1 hz.1).ne')
    exact (continuousOn_const.mul hp).mul
      ((scalarFunctionalProduct L n).cont.comp continuous_snd).continuousOn
  derivative := by
    intro n x hx v w
    exact affineRpowJets_hasLineDerivAt α q₀ L n x (hpos x hx) v w

def smoothDirections_affineSqrt (q₀ : ℝ) (L : E →L[ℝ] ℝ)
    {U : Set E} (hU : IsOpen U) (hpos : ∀ x ∈ U, 0 < q₀ + L x) :
    SmoothDirections U (fun x : E => Real.sqrt (q₀ + L x)) :=
  (smoothDirections_affineRpow (1 / 2) q₀ L hU hpos).congr
    (fun x _ => (Real.sqrt_eq_rpow _).symm)

theorem smoothDirections_affineSqrt_D_apply (q₀ : ℝ) (L : E →L[ℝ] ℝ)
    {U : Set E} (hU : IsOpen U) (hpos : ∀ x ∈ U, 0 < q₀ + L x)
    (n : ℕ) (x : E) (v : Fin n → E) :
    (smoothDirections_affineSqrt q₀ L hU hpos).D n x v =
      rpowJetCoefficient (1 / 2) n * (q₀ + L x) ^ ((1 / 2 : ℝ) - (n : ℝ)) *
        ∏ i, L (v i) :=
  affineRpowJets_apply (1 / 2) q₀ L n x v

end AffineParameterJets

/-- The exact cancellation of N singular denominator powers against
N endpoint factors. The upper bound supplies only the remaining square root. -/
theorem endpoint_rpow_half_sub_mul_pow_le
    {q δ c M : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : c * δ ≤ q) (hupper : q ≤ M * δ) (N : ℕ) :
    δ ^ N * q ^ ((1 / 2 : ℝ) - (N : ℝ)) ≤
      (Real.sqrt M / c ^ N) * Real.sqrt δ := by
  have hq : 0 < q := (mul_pos hc hδ).trans_le hlower
  rw [Real.rpow_sub_natCast hq.ne', ← Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt q ≤ Real.sqrt M * Real.sqrt δ := by
    simpa only [Real.sqrt_mul hM] using Real.sqrt_le_sqrt hupper
  have hden : c ^ N * δ ^ N ≤ q ^ N := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_pos hc hδ).le hlower N
  have hdiv : Real.sqrt q / q ^ N ≤
      (Real.sqrt M * Real.sqrt δ) / (c ^ N * δ ^ N) := by
    apply (div_le_div_iff₀ (pow_pos hq N) (mul_pos (pow_pos hc N) (pow_pos hδ N))).mpr
    exact mul_le_mul hsqrt hden (mul_nonneg (pow_nonneg hc.le N)
      (pow_nonneg hδ.le N))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    δ ^ N * (Real.sqrt q / q ^ N) ≤
        δ ^ N * ((Real.sqrt M * Real.sqrt δ) / (c ^ N * δ ^ N)) :=
      mul_le_mul_of_nonneg_left hdiv (pow_nonneg hδ.le N)
    _ = (Real.sqrt M / c ^ N) * Real.sqrt δ := by
      field_simp [pow_ne_zero N hc.ne', pow_ne_zero N hδ.ne']
      <;> ring

/-- Every ordinary jet of the shifted square-root power has the same
half-distance remainder after its k+N endpoint factors are restored. -/
theorem endpoint_rpowJet_bound
    {q δ c M : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : c * δ ≤ q) (hupper : q ≤ M * δ) (k N : ℕ) :
    δ ^ (k + N) *
        |iteratedDeriv N (fun t : ℝ => t ^ ((1 / 2 : ℝ) - (k : ℝ))) q| ≤
      (|rpowJetCoefficient ((1 / 2 : ℝ) - (k : ℝ)) N| *
        (Real.sqrt M / c ^ (k + N))) * Real.sqrt δ := by
  rw [iteratedDeriv_rpow_eq, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ((mul_pos hc hδ).trans_le hlower).le _)]
  rw [show (1 / 2 : ℝ) - (k : ℝ) - (N : ℝ) =
    (1 / 2 : ℝ) - ((k + N : ℕ) : ℝ) by push_cast; ring]
  calc
    _ = |rpowJetCoefficient ((1 / 2 : ℝ) - (k : ℝ)) N| *
        (δ ^ (k + N) * q ^ ((1 / 2 : ℝ) - ((k + N : ℕ) : ℝ))) := by ring
    _ ≤ |rpowJetCoefficient ((1 / 2 : ℝ) - (k : ℝ)) N| *
        ((Real.sqrt M / c ^ (k + N)) * Real.sqrt δ) :=
      mul_le_mul_of_nonneg_left
        (endpoint_rpow_half_sub_mul_pow_le hδ hc hM hlower hupper (k + N))
        (abs_nonneg _)
    _ = _ := by ring

/-- Actual parameter jets of an affine optical square root obey the
endpoint estimate for arbitrary direction factors, including k=0. -/
theorem affineSqrt_parameterJet_endpoint_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (q₀ : ℝ) (L : E →L[ℝ] ℝ) {U : Set E} (hU : IsOpen U)
    (hpos : ∀ x ∈ U, 0 < q₀ + L x)
    {δ c M : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hM : 0 ≤ M)
    (k : ℕ) (x : E) (v : Fin k → E) (B : Fin k → ℝ)
    (hB : ∀ i, 0 ≤ B i)
    (hlower : c * δ ≤ q₀ + L x) (hupper : q₀ + L x ≤ M * δ)
    (hL : ∀ i, |L (v i)| ≤ B i * δ) :
    |(smoothDirections_affineSqrt q₀ L hU hpos).D k x v| ≤
      (|rpowJetCoefficient (1 / 2) k| * (Real.sqrt M / c ^ k) *
        ∏ i, B i) * Real.sqrt δ := by
  rw [smoothDirections_affineSqrt_D_apply, abs_mul, abs_mul, Finset.abs_prod,
    abs_of_nonneg (Real.rpow_nonneg ((mul_pos hc hδ).trans_le hlower).le _)]
  have hp : ∏ i, |L (v i)| ≤ (∏ i, B i) * δ ^ k := by
    calc
      _ ≤ ∏ i, B i * δ :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hL i)
      _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
  have hcoef := endpoint_rpow_half_sub_mul_pow_le hδ hc hM hlower hupper k
  calc
    _ ≤ (|rpowJetCoefficient (1 / 2) k| *
        (q₀ + L x) ^ ((1 / 2 : ℝ) - (k : ℝ))) * ((∏ i, B i) * δ ^ k) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg _)
        (Real.rpow_nonneg ((mul_pos hc hδ).trans_le hlower).le _))
    _ = (|rpowJetCoefficient (1 / 2) k| * ∏ i, B i) *
        (δ ^ k * (q₀ + L x) ^ ((1 / 2 : ℝ) - (k : ℝ))) := by ring
    _ ≤ (|rpowJetCoefficient (1 / 2) k| * ∏ i, B i) *
        ((Real.sqrt M / c ^ k) * Real.sqrt δ) :=
      mul_le_mul_of_nonneg_left hcoef
        (mul_nonneg (abs_nonneg _) (Finset.prod_nonneg (fun i _ => hB i)))
    _ = _ := by ring

/-- The finite scalar coefficient left by a spatial partition after all
its true endpoint factors have cancelled the square-root singularity. -/
def endpointPowerCompositionMajorant (c M : ℝ) (A : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ d : OrderedFinpartition n,
    (|rpowJetCoefficient ((1 / 2 : ℝ) - (k : ℝ)) d.length| *
      (Real.sqrt M / c ^ (k + d.length))) * ∏ i, A (d.partSize i)

theorem endpointPowerCompositionMajorant_nonneg
    {c M : ℝ} (hc : 0 ≤ c) (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) (k n : ℕ) :
    0 ≤ endpointPowerCompositionMajorant c M A k n := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg
    (mul_nonneg (abs_nonneg _) (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hc _)))
    (Finset.prod_nonneg (fun i _ => hA _))

/-- Actual spatial differentiation of the singular scalar outer power.
The k reserved endpoint factors are precisely those carried by k
parameter directions in the affine-square-root formula. -/
theorem endpoint_rpowComposition_radial_bound
    {q : ℝ → ℝ} {r δ c M : ℝ}
    (hq : ContDiffAt ℝ ∞ q r) (hδ : 0 < δ) (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : c * δ ≤ q r) (hupper : q r ≤ M * δ)
    (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) (k n : ℕ)
    (hjet : ∀ j, j ≤ n → δ ^ j * |iteratedDeriv j q r| ≤ δ * A j) :
    δ ^ (n + k) *
        |iteratedDeriv n (fun t => q t ^ ((1 / 2 : ℝ) - (k : ℝ))) r| ≤
      Real.sqrt δ * endpointPowerCompositionMajorant c M A k n := by
  have hqpos : 0 < q r := (mul_pos hc hδ).trans_le hlower
  have houter : ContDiffAt ℝ ∞
      (fun t : ℝ => t ^ ((1 / 2 : ℝ) - (k : ℝ))) (q r) :=
    Real.contDiffAt_rpow_const_of_ne hqpos.ne'
  have hformula := iteratedDeriv_comp_eq_sum_orderedFinpartition houter hq
    (by simp : (n : ℕ∞ω) ≤ ∞)
  simp only [Function.comp_def] at hformula
  rw [hformula, endpointPowerCompositionMajorant, Finset.mul_sum]
  calc
    _ ≤ δ ^ (n + k) * ∑ d : OrderedFinpartition n,
        |iteratedDeriv d.length
          (fun t : ℝ => t ^ ((1 / 2 : ℝ) - (k : ℝ))) (q r) *
            ∏ i, iteratedDeriv (d.partSize i) q r| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (pow_nonneg hδ.le _)
    _ = ∑ d : OrderedFinpartition n, δ ^ (n + k) *
        |iteratedDeriv d.length
          (fun t : ℝ => t ^ ((1 / 2 : ℝ) - (k : ℝ))) (q r) *
            ∏ i, iteratedDeriv (d.partSize i) q r| := Finset.mul_sum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d _
      have hp : δ ^ n * (∏ i, |iteratedDeriv (d.partSize i) q r|) ≤
          δ ^ d.length * ∏ i, A (d.partSize i) := by
        calc
          _ = ∏ i, δ ^ d.partSize i * |iteratedDeriv (d.partSize i) q r| := by
            rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
              orderedFinpartition_sum_partSize]
          _ ≤ ∏ i, δ * A (d.partSize i) :=
            Finset.prod_le_prod₀
              (fun i _ => mul_nonneg (pow_nonneg hδ.le _) (abs_nonneg _))
              (fun i _ => hjet _ (d.partSize_le i))
          _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
      have houterBound := endpoint_rpowJet_bound hδ hc hM hlower hupper k d.length
      rw [abs_mul, Finset.abs_prod]
      calc
        _ = (δ ^ k * |iteratedDeriv d.length
              (fun t : ℝ => t ^ ((1 / 2 : ℝ) - (k : ℝ))) (q r)|) *
            (δ ^ n * ∏ i, |iteratedDeriv (d.partSize i) q r|) := by
          rw [pow_add]
          ring
        _ ≤ (δ ^ k * |iteratedDeriv d.length
              (fun t : ℝ => t ^ ((1 / 2 : ℝ) - (k : ℝ))) (q r)|) *
            (δ ^ d.length * ∏ i, A (d.partSize i)) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg (pow_nonneg hδ.le _) (abs_nonneg _))
        _ = (δ ^ (k + d.length) * |iteratedDeriv d.length
              (fun t : ℝ => t ^ ((1 / 2 : ℝ) - (k : ℝ))) (q r)|) *
            ∏ i, A (d.partSize i) := by rw [pow_add]; ring
        _ ≤ ((|rpowJetCoefficient ((1 / 2 : ℝ) - (k : ℝ)) d.length| *
              (Real.sqrt M / c ^ (k + d.length))) * Real.sqrt δ) *
            ∏ i, A (d.partSize i) :=
          mul_le_mul_of_nonneg_right houterBound
            (Finset.prod_nonneg (fun i _ => hA _))
        _ = _ := by ring

theorem endpoint_sqrt_radial_bound
    {q : ℝ → ℝ} {r δ c M : ℝ}
    (hq : ContDiffAt ℝ ∞ q r) (hδ : 0 < δ) (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : c * δ ≤ q r) (hupper : q r ≤ M * δ)
    (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) (n : ℕ)
    (hjet : ∀ j, j ≤ n → δ ^ j * |iteratedDeriv j q r| ≤ δ * A j) :
    δ ^ n * |iteratedDeriv n (fun t => Real.sqrt (q t)) r| ≤
      Real.sqrt δ * endpointPowerCompositionMajorant c M A 0 n := by
  simpa only [Nat.add_zero, Nat.cast_zero, sub_zero, ← Real.sqrt_eq_rpow] using
    endpoint_rpowComposition_radial_bound hq hδ hc hM hlower hupper A hA 0 n hjet

end ContinuousFlexibility.Analysis
