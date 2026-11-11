import ContinuousFlexibility.Statements.Analysis
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Smoothing, interpolation, and tame retractions

The smoothing family is the actual exponential sequence cutoff or the
conjugated family `P ∘ S_N ∘ J` of a tame retraction. Both losses of the
retraction are retained. Interpolation follows by balancing the two
smoothing estimates at one integer cutoff, including vectors with zero
low seminorm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology NNReal
open ContinuousFlexibility.Statements

theorem hasSmoothing_exponentialSequence (B : Type*) [NormedAddCommGroup B]
    [NormedSpace ℝ B] : HasSmoothing (exponentialSequenceSeminorm B) := by
  refine ⟨0, 0, exponentialSequenceSmoothing B, ?_, ?_,
    tendsto_exponentialSequenceSmoothing B⟩
  · intro m n _ hmn
    refine ⟨1, zero_le_one, fun N x => ?_⟩
    simpa only [Nat.cast_zero, add_zero, one_mul] using
      exponentialSequenceSmoothing_forward B hmn N x
  · intro m n _ hmn
    refine ⟨1, zero_le_one, fun N x => ?_⟩
    simpa only [Nat.cast_zero, sub_zero, one_mul, neg_mul] using
      exponentialSequenceSmoothing_tail B hmn N x

section Retraction

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Transfer smoothing through an arbitrary fixed-loss tame retraction.
The total smoothing loss is the old loss plus both retraction losses. -/
theorem hasSmoothing_of_tameRetraction {p : ℕ → Seminorm ℝ E}
    {q : ℕ → Seminorm ℝ F} (hp : Monotone p)
    (hR : TameRetraction p q) (hS : HasSmoothing q) : HasSmoothing p := by
  obtain ⟨J, P, hPJ, ⟨rJ, bJ, hJ⟩, ⟨rP, bP, hP⟩⟩ := hR
  obtain ⟨bS, l, S, hforward, htail, happrox⟩ := hS
  let b : ℕ := max bP (max bJ bS) + rJ
  let loss : ℕ := rP + rJ + l
  let T : ℕ → E →L[ℝ] E := fun N => P.comp ((S N).comp J)
  have hbP {m : ℕ} (hm : b ≤ m) : bP ≤ m := by dsimp [b] at hm; omega
  have hbJ {m : ℕ} (hm : b ≤ m) : bJ ≤ m - rJ := by dsimp [b] at hm; omega
  have hbS {m : ℕ} (hm : b ≤ m) : bS ≤ m - rJ := by dsimp [b] at hm; omega
  have hrJ {m : ℕ} (hm : b ≤ m) : rJ ≤ m := by dsimp [b] at hm; omega
  have hT (N : ℕ) (x : E) : T N x = P (S N (J x)) := by
    simp only [T, ContinuousLinearMap.comp_apply]
  refine ⟨b, loss, T, ?_, ?_, ?_⟩
  · intro m n hm hmn
    obtain ⟨CP, hCP⟩ := hP n ((hbP hm).trans hmn)
    obtain ⟨CJ, hCJ⟩ := hJ (m - rJ) (hbJ hm)
    obtain ⟨CS, hCS0, hCS⟩ :=
      hforward (m - rJ) (n + rP) (hbS hm) (by omega)
    refine ⟨CP * CS * CJ, mul_nonneg (mul_nonneg CP.2 hCS0) CJ.2, fun N x => ?_⟩
    have he : (((n + rP : ℕ) : ℝ) - (m - rJ : ℕ) + l) =
        (n : ℝ) - m + loss := by
      simp only [Nat.cast_add, Nat.cast_sub (hrJ hm), loss]
      ring
    have hj : q (m - rJ) (J x) ≤ (CJ : ℝ) * p m x := by
      simpa only [ContinuousLinearMap.coe_coe, Nat.sub_add_cancel (hrJ hm)] using hCJ x
    rw [hT]
    calc
      p n (P (S N (J x))) ≤ (CP : ℝ) * q (n + rP) (S N (J x)) := hCP _
      _ ≤ (CP : ℝ) * (CS * Real.exp (((n : ℝ) - m + loss) * N) *
          q (m - rJ) (J x)) := by
        apply mul_le_mul_of_nonneg_left _ CP.2
        simpa only [he] using hCS N (J x)
      _ ≤ (CP : ℝ) * (CS * Real.exp (((n : ℝ) - m + loss) * N) *
          ((CJ : ℝ) * p m x)) := by
        apply mul_le_mul_of_nonneg_left _ CP.2
        exact mul_le_mul_of_nonneg_left hj (mul_nonneg hCS0 (Real.exp_pos _).le)
      _ = _ := by ring
  · intro m n hm hmn
    have hn : b ≤ n := hm.trans hmn
    obtain ⟨CP, hCP⟩ := hP m (hbP hm)
    obtain ⟨CJ, hCJ⟩ := hJ (n - rJ) (hbJ hn)
    have hj (x : E) : q (n - rJ) (J x) ≤ (CJ : ℝ) * p n x := by
      simpa only [ContinuousLinearMap.coe_coe, Nat.sub_add_cancel (hrJ hn)] using hCJ x
    have he : (((n - rJ : ℕ) : ℝ) - (m + rP : ℕ) - l) =
        (n : ℝ) - m - loss := by
      simp only [Nat.cast_sub (hrJ hn), Nat.cast_add, loss]
      ring
    by_cases hgap : m + rP ≤ n - rJ
    · obtain ⟨CS, hCS0, hCS⟩ := htail (m + rP) (n - rJ) (by
        have := hbS hm; omega) hgap
      refine ⟨CP * CS * CJ, mul_nonneg (mul_nonneg CP.2 hCS0) CJ.2, fun N x => ?_⟩
      have hdiff : x - T N x = P (J x - S N (J x)) := by rw [map_sub, hPJ, hT]
      rw [hdiff]
      calc
        p m (P (J x - S N (J x))) ≤ (CP : ℝ) *
            q (m + rP) (J x - S N (J x)) := hCP _
        _ ≤ (CP : ℝ) * (CS * Real.exp (-((n : ℝ) - m - loss) * N) *
            q (n - rJ) (J x)) := by
          apply mul_le_mul_of_nonneg_left _ CP.2
          simpa only [he] using hCS N (J x)
        _ ≤ (CP : ℝ) * (CS * Real.exp (-((n : ℝ) - m - loss) * N) *
            ((CJ : ℝ) * p n x)) := by
          apply mul_le_mul_of_nonneg_left _ CP.2
          exact mul_le_mul_of_nonneg_left (hj x) (mul_nonneg hCS0 (Real.exp_pos _).le)
        _ = _ := by ring
    · have hgap' : n - rJ ≤ m + rP := by omega
      obtain ⟨CS, hCS0, hCS⟩ := hforward (n - rJ) (m + rP) (hbS hn) hgap'
      have he' : (((m + rP : ℕ) : ℝ) - (n - rJ : ℕ) + l) =
          -((n : ℝ) - m - loss) := by
        simp only [Nat.cast_sub (hrJ hn), Nat.cast_add, loss]
        ring
      refine ⟨1 + CP * CS * CJ, by positivity, fun N x => ?_⟩
      have hnonneg : 0 ≤ -((n : ℝ) - m - loss) := by
        have hgapR : ((n - rJ : ℕ) : ℝ) ≤ (m + rP : ℕ) := Nat.cast_le.mpr hgap'
        rw [← he']
        exact add_nonneg (sub_nonneg.mpr hgapR) (Nat.cast_nonneg _)
      have hExp : 1 ≤ Real.exp (-((n : ℝ) - m - loss) * N) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg hnonneg (Nat.cast_nonneg _))
      have htx : p m (T N x) ≤ (CP : ℝ) * CS * CJ *
          Real.exp (-((n : ℝ) - m - loss) * N) * p n x := by
        rw [hT]
        calc
          p m (P (S N (J x))) ≤ (CP : ℝ) * q (m + rP) (S N (J x)) := hCP _
          _ ≤ (CP : ℝ) * (CS * Real.exp (-((n : ℝ) - m - loss) * N) *
              q (n - rJ) (J x)) := by
            apply mul_le_mul_of_nonneg_left _ CP.2
            simpa only [he'] using hCS N (J x)
          _ ≤ (CP : ℝ) * (CS * Real.exp (-((n : ℝ) - m - loss) * N) *
              ((CJ : ℝ) * p n x)) := by
            apply mul_le_mul_of_nonneg_left _ CP.2
            exact mul_le_mul_of_nonneg_left (hj x) (mul_nonneg hCS0 (Real.exp_pos _).le)
          _ = _ := by ring
      calc
        p m (x - T N x) ≤ p m x + p m (T N x) := map_sub_le_add _ _ _
        _ ≤ p n x + (CP : ℝ) * CS * CJ *
            Real.exp (-((n : ℝ) - m - loss) * N) * p n x := add_le_add (hp hmn x) htx
        _ ≤ Real.exp (-((n : ℝ) - m - loss) * N) * p n x +
            (CP : ℝ) * CS * CJ * Real.exp (-((n : ℝ) - m - loss) * N) * p n x := by
          apply add_le_add_right
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hExp (apply_nonneg (p n) x)
        _ = _ := by ring
  · intro x
    have ht := (P.continuous.tendsto (J x)).comp (happrox (J x))
    simpa only [Function.comp_def, hPJ, ← hT] using ht

end Retraction

/-! ## Interpolation from one integer smoothing cutoff -/

private theorem interpolation_of_exponential_bounds
    {A B C u v K L : ℝ} (hA : 0 ≤ A) (hAC : A ≤ C)
    (hu : 0 < u) (hv : 0 < v) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hbound : ∀ N : ℕ,
      B ≤ K * Real.exp (u * N) * A + L * Real.exp (-v * N) * C) :
    B ≤ (K * Real.exp u + L) * A ^ (v / (u + v)) * C ^ (u / (u + v)) := by
  have hC : 0 ≤ C := hA.trans hAC
  by_cases hAz : A = 0
  · have ht : Tendsto (fun N : ℕ => Real.exp (-v * N)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith : -v < 0))
    have ht' : Tendsto (fun N : ℕ => L * Real.exp (-v * N) * C) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using (ht.const_mul L).mul_const C
    have hB : B ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht'
      (Eventually.of_forall (fun N => by simpa only [hAz, mul_zero, zero_add] using hbound N))
    exact hB.trans (by positivity)
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hCpos : 0 < C := hApos.trans_le hAC
  have huv : 0 < u + v := add_pos hu hv
  let t : ℝ := (Real.log C - Real.log A) / (u + v)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr (Real.log_le_log hApos hAC)) huv.le
  let N : ℕ := ⌈t⌉₊
  have hNt : t ≤ (N : ℝ) := Nat.le_ceil t
  have hNt' : (N : ℝ) ≤ t + 1 := (Nat.ceil_lt_add_one ht).le
  let M : ℝ := A ^ (v / (u + v)) * C ^ (u / (u + v))
  have hbalance₁ : Real.exp (u * t) * A = M := by
    dsimp [M]
    rw [Real.rpow_def_of_pos hApos, Real.rpow_def_of_pos hCpos, ← Real.exp_add]
    calc
      Real.exp (u * t) * A = Real.exp (u * t) * Real.exp (Real.log A) := by
        rw [Real.exp_log hApos]
      _ = Real.exp (u * t + Real.log A) := (Real.exp_add _ _).symm
      _ = _ := by
        congr 1
        dsimp [t]
        field_simp [ne_of_gt huv]
        ring
  have hbalance₂ : Real.exp (-v * t) * C = M := by
    dsimp [M]
    rw [Real.rpow_def_of_pos hApos, Real.rpow_def_of_pos hCpos, ← Real.exp_add]
    calc
      Real.exp (-v * t) * C = Real.exp (-v * t) * Real.exp (Real.log C) := by
        rw [Real.exp_log hCpos]
      _ = Real.exp (-v * t + Real.log C) := (Real.exp_add _ _).symm
      _ = _ := by
        congr 1
        dsimp [t]
        field_simp [ne_of_gt huv]
        ring
  have hfirst : K * Real.exp (u * N) * A ≤ K * Real.exp u * M := by
    calc
      K * Real.exp (u * N) * A ≤ K * Real.exp (u * (t + 1)) * A := by
        apply mul_le_mul_of_nonneg_right _ hA
        apply mul_le_mul_of_nonneg_left _ hK
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hNt' hu.le)
      _ = K * Real.exp u * (Real.exp (u * t) * A) := by
        rw [mul_add, mul_one, Real.exp_add]
        ring
      _ = _ := by rw [hbalance₁]
  have hsecond : L * Real.exp (-v * N) * C ≤ L * M := by
    calc
      L * Real.exp (-v * N) * C ≤ L * Real.exp (-v * t) * C := by
        apply mul_le_mul_of_nonneg_right _ hC
        apply mul_le_mul_of_nonneg_left _ hL
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hNt (by linarith))
      _ = L * M := by rw [mul_assoc, hbalance₂]
  calc
    B ≤ K * Real.exp (u * N) * A + L * Real.exp (-v * N) * C := hbound N
    _ ≤ K * Real.exp u * M + L * M := add_le_add hfirst hsecond
    _ = _ := by dsimp [M]; ring

section Interpolation

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- The fixed smoothing loss gives precisely the shifted interpolation
exponents in `HasInterpolation`, with one common base and loss. -/
theorem hasInterpolation_of_hasSmoothing {p : ℕ → Seminorm ℝ E}
    (hp : Monotone p) (hS : HasSmoothing p) : HasInterpolation p := by
  obtain ⟨base, loss, S, hforward, htail, _⟩ := hS
  refine ⟨base, loss, fun a b c ha hab hbc => ?_⟩
  have hac : a ≤ c := by omega
  have hbc' : b ≤ c := by omega
  obtain ⟨K, hK, hKb⟩ := hforward a b ha hab.le
  obtain ⟨L, hL, hLb⟩ := htail b c (ha.trans hab.le) hbc'
  let u : ℝ := (b : ℝ) - a + loss
  let v : ℝ := (c : ℝ) - b - loss
  have hu : 0 < u := by
    have habR : (a : ℝ) < b := Nat.cast_lt.mpr hab
    have hlR : (0 : ℝ) ≤ loss := Nat.cast_nonneg loss
    dsimp [u]
    linarith
  have hv : 0 < v := by
    have hbcR : (b : ℝ) + loss < c := by exact_mod_cast hbc
    dsimp [v]
    linarith
  have huv : u + v = (c : ℝ) - a := by dsimp [u, v]; ring
  refine ⟨K * Real.exp u + L, add_nonneg (mul_nonneg hK (Real.exp_pos _).le) hL,
    fun x => ?_⟩
  have hbound (N : ℕ) : p b x ≤
      K * Real.exp (u * N) * p a x + L * Real.exp (-v * N) * p c x := by
    calc
      p b x ≤ p b (S N x) + p b (x - S N x) := by
        calc
          p b x = p b ((x - S N x) + S N x) := by rw [sub_add_cancel]
          _ ≤ p b (x - S N x) + p b (S N x) := map_add_le_add _ _ _
          _ = _ := add_comm _ _
      _ ≤ _ := add_le_add (hKb N x) (hLb N x)
  have hi := interpolation_of_exponential_bounds (apply_nonneg (p a) x) (hp hac x)
    hu hv hK hL hbound
  simpa only [huv] using hi

end Interpolation

end ContinuousFlexibility.Analysis
