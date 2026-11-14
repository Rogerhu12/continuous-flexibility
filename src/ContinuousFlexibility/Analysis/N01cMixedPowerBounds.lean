module

public import ContinuousFlexibility.Analysis.N01cFiniteParameterProducts
public import ContinuousFlexibility.Analysis.N01cOneHighProducts
public import ContinuousFlexibility.Analysis.N01cDistributedRadialProducts

/-!
# Spatial orders in actual parameter-jet estimates

The real power attached to an actual spatial jet is its order divided by
the fixed top order plus one. Products add these orders before any
one-high normalization. Neither multiplication nor scalar composition
changes the base or the spatial loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Actual spatial smoothness and actual parameter towers of its mixed jets. -/
structure MixedJetRegularity (U : Set X) (Ω : Set PolarPoint)
    (f : X → PolarPoint → ℝ) where
  spatial : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) Ω
  parameter : ∀ a b : ℕ, ∀ q ∈ Ω,
    SmoothDirections U (fun x => mixedDerivative a b (f x) q)

/-- The weight for a positive parameter derivative. The original
function itself is allowed an unweighted envelope bound. -/
def parameterHeightWeight (H : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else H

/-- A bound before multilinear normalization. The spatial order is kept
in its exponent, and R can bound any chosen family of parameter slots. -/
def MixedPowerBounds (p : ℕ → Seminorm ℝ X) (center : X)
    (base loss : ℕ) (U : Set X) (Ω : Set PolarPoint)
    (H E : PolarPoint → ℝ) (f : X → PolarPoint → ℝ) : Prop :=
  ∀ K s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
    ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
    ∀ q ∈ Ω, ∀ J : SmoothDirections U (fun x => mixedDerivative a b (f x) q),
    ∀ x ∈ U, p base (x - center) ≤ 1 →
    ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → p (s + loss) (x - center) ≤ R →
      (∀ i, p (s + loss) (v i) ≤ R) →
      ‖J.D k x v‖ ≤ C * E q ^ A * parameterHeightWeight (H q) k *
        R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))

theorem parameterHeightWeight_nonneg {H : ℝ} (hH : 0 ≤ H) (k : ℕ) :
    0 ≤ parameterHeightWeight H k := by
  unfold parameterHeightWeight
  split_ifs <;> positivity

theorem spatialOrder_fraction_nonneg (n s : ℕ) :
    0 ≤ (n : ℝ) / ((s : ℝ) + 1) := by positivity

theorem spatialOrder_fraction_le_one {n s : ℕ} (hn : n ≤ s) :
    (n : ℝ) / ((s : ℝ) + 1) ≤ 1 := by
  apply (div_le_one (by positivity : 0 < (s : ℝ) + 1)).mpr
  have h : (n : ℝ) ≤ s := by exact_mod_cast hn
  linarith

theorem rpow_spatialOrder_mul {R : ℝ} (hR : 0 < R) (a b s : ℕ) :
    R ^ ((a : ℝ) / ((s : ℝ) + 1)) *
      R ^ ((b : ℝ) / ((s : ℝ) + 1)) =
        R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  rw [← Real.rpow_add hR]
  congr 1
  push_cast
  ring

/-- The same interpolation base and loss control every individual jet
by its own spatial power. -/
theorem exists_seminorm_spatialPower_bound
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    (hinterp : HasInterpolation p) (offset : ℕ) :
    ∃ base loss : ℕ, ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ, n ≤ s → ∀ x : X, p base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → p (s + loss) x ≤ R →
        p (n + offset) x ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1)) := by
  classical
  obtain ⟨base, loss, hb⟩ := exists_interpolatedJetBounds p hp hinterp offset
  refine ⟨base, loss, fun s => ?_⟩
  choose c hc hcb using
    (fun n : Fin (s + 1) => hb s n.val (Nat.le_of_lt_succ n.isLt))
  let C : ℝ := 2 * (1 + ∑ n : Fin (s + 1), c n)
  have hc0 (n : Fin (s + 1)) : 0 ≤ c n := zero_le_one.trans (hc n)
  have hsum : 0 ≤ ∑ n : Fin (s + 1), c n :=
    Finset.sum_nonneg (fun n _ => hc0 n)
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, fun n hn x hx R hR hhigh => ?_⟩
  let i : Fin (s + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hi : c i ≤ 1 + ∑ n : Fin (s + 1), c n :=
    (Finset.single_le_sum (fun j _ => hc0 j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hθ := spatialOrder_fraction_nonneg n s
  have hθ1 := spatialOrder_fraction_le_one hn
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hpow :
      (1 + p (s + loss) x) ^ ((n : ℝ) / ((s : ℝ) + 1)) ≤
        2 * R ^ ((n : ℝ) / ((s : ℝ) + 1)) := by
    calc
      _ ≤ (2 * R) ^ ((n : ℝ) / ((s : ℝ) + 1)) :=
        Real.rpow_le_rpow (by positivity) (by linarith) hθ
      _ = (2 : ℝ) ^ ((n : ℝ) / ((s : ℝ) + 1)) *
          R ^ ((n : ℝ) / ((s : ℝ) + 1)) :=
        Real.mul_rpow (by norm_num) hR0.le
      _ ≤ 2 * R ^ ((n : ℝ) / ((s : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num) hθ1)
          (Real.rpow_nonneg hR0.le _)
  calc
    _ ≤ c i * (1 + p (s + loss) x) ^ ((n : ℝ) / ((s : ℝ) + 1)) :=
      hcb i x hx
    _ ≤ c i * (2 * R ^ ((n : ℝ) / ((s : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hpow (hc0 i)
    _ ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1)) := by
      dsimp only [C]
      nlinarith [Real.rpow_nonneg hR0.le ((n : ℝ) / ((s : ℝ) + 1))]

/-- Smoothness of all scalar outer derivatives on the same open set. -/
theorem contDiffOn_iteratedDeriv_open {V : Set ℝ} {g : ℝ → ℝ}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n g) V := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen hV (by simp)

namespace MixedJetRegularity

variable {U : Set X} {Ω : Set PolarPoint} {f g : X → PolarPoint → ℝ}

/-- Equality on the actual open spatial domain transports genuine jets. -/
def congr (F : MixedJetRegularity U Ω f) (hΩ : IsOpen Ω)
    (hg : ∀ x ∈ U, ContDiffOn ℝ ∞ (g x) Ω)
    (heq : ∀ x ∈ U, EqOn (f x) (g x) Ω) :
    MixedJetRegularity U Ω g where
  spatial := hg
  parameter a b q hq := (F.parameter a b q hq).congr (fun x hx =>
    mixedDerivative_eq_of_eqOn hΩ (F.spatial x hx) (hg x hx)
      (heq x hx) a b hq)

/-- A finite-dimensional smooth kernel acts on the actual input towers. -/
def finiteComp {m : ℕ} {F : Fin m → X → PolarPoint → ℝ}
    (J : ∀ i, MixedJetRegularity U Ω (F i))
    (hU : IsOpen U) (hΩ : IsOpen Ω) {V : Set (Fin m → ℝ)}
    (hV : IsOpen V) {G : (Fin m → ℝ) → ℝ}
    (hG : ContDiffOn ℝ ∞ G V)
    (hmap : ∀ x ∈ U, ∀ q ∈ Ω, (fun i => F i x q) ∈ V) :
    MixedJetRegularity U Ω (fun x q => G (fun i => F i x q)) where
  spatial x hx := hG.comp (contDiffOn_pi.mpr (fun i => (J i).spatial x hx))
    (hmap x hx)
  parameter a b q hq := smoothDirections_mixedDerivative_comp hU hΩ hV
    (fun x hx => contDiffOn_pi.mpr (fun i => (J i).spatial x hx))
    hG hmap q hq (fun a b i => (J i).parameter a b q hq) a b

def scalarComp (F : MixedJetRegularity U Ω f)
    (hU : IsOpen U) (hΩ : IsOpen Ω) {V : Set ℝ} (hV : IsOpen V)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G V)
    (hmap : ∀ x ∈ U, MapsTo (f x) Ω V) :
    MixedJetRegularity U Ω (fun x q => G (f x q)) := by
  let W : Set (Fin 1 → ℝ) := {y | y 0 ∈ V}
  have hW : IsOpen W := hV.preimage (continuous_apply 0)
  exact finiteComp (fun _ : Fin 1 => F) hU hΩ hW
    (hG.comp (contDiff_apply ℝ ℝ 0).contDiffOn (fun _ hy => hy))
    (fun x hx q hq => hmap x hx hq)

def add (F : MixedJetRegularity U Ω f) (G : MixedJetRegularity U Ω g)
    (hU : IsOpen U) (hΩ : IsOpen Ω) :
    MixedJetRegularity U Ω (fun x q => f x q + g x q) := by
  let P : Fin 2 → X → PolarPoint → ℝ := Fin.cases f (fun _ : Fin 1 => g)
  let J : ∀ i : Fin 2, MixedJetRegularity U Ω (P i) :=
    Fin.cases (motive := fun i => MixedJetRegularity U Ω (P i))
      (show MixedJetRegularity U Ω (P 0) from F)
      (fun i : Fin 1 => show MixedJetRegularity U Ω (P i.succ) from G)
  have h : MixedJetRegularity U Ω (fun x q => P 0 x q + P 1 x q) :=
    finiteComp (m := 2) (F := P) (G := fun y : Fin 2 → ℝ => y 0 + y 1)
      J hU hΩ isOpen_univ
      ((contDiff_apply ℝ ℝ (0 : Fin 2)).add (contDiff_apply ℝ ℝ 1)).contDiffOn
      (fun _ _ _ _ => mem_univ _)
  have hP₀ : P 0 = f := by simp only [P, Fin.cases_zero]
  have hP₁ : P 1 = g := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from by decide]
    simp only [P, Fin.cases_succ]
  simpa only [hP₀, hP₁] using h

def mul (F : MixedJetRegularity U Ω f) (G : MixedJetRegularity U Ω g)
    (hU : IsOpen U) (hΩ : IsOpen Ω) :
    MixedJetRegularity U Ω (fun x q => f x q * g x q) := by
  let P : Fin 2 → X → PolarPoint → ℝ := Fin.cases f (fun _ : Fin 1 => g)
  let J : ∀ i : Fin 2, MixedJetRegularity U Ω (P i) :=
    Fin.cases (motive := fun i => MixedJetRegularity U Ω (P i))
      (show MixedJetRegularity U Ω (P 0) from F)
      (fun i : Fin 1 => show MixedJetRegularity U Ω (P i.succ) from G)
  have h : MixedJetRegularity U Ω (fun x q => P 0 x q * P 1 x q) :=
    finiteComp (m := 2) (F := P) (G := fun y : Fin 2 → ℝ => y 0 * y 1)
      J hU hΩ isOpen_univ
      ((contDiff_apply ℝ ℝ (0 : Fin 2)).mul (contDiff_apply ℝ ℝ 1)).contDiffOn
      (fun _ _ _ _ => mem_univ _)
  have hP₀ : P 0 = f := by simp only [P, Fin.cases_zero]
  have hP₁ : P 1 = g := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from by decide]
    simp only [P, Fin.cases_succ]
  simpa only [hP₀, hP₁] using h

def const (hU : IsOpen U) (hΩ : IsOpen Ω) (c : ℝ) :
    MixedJetRegularity U Ω (fun _ _ => c) where
  spatial _ _ := contDiffOn_const
  parameter a b q _ := smoothDirections_constant hU (mixedDerivative a b (fun _ => c) q)

end MixedJetRegularity

/-- Replacing the actual field by an equal field does not alter its
parameter bounds or its interpolation indices. -/
theorem MixedPowerBounds.congr
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}
    {f g : X → PolarPoint → ℝ}
    (hf : MixedPowerBounds p center base loss U Ω H E f)
    (F : MixedJetRegularity U Ω f) (G : MixedJetRegularity U Ω g)
    (hΩ : IsOpen Ω) (heq : ∀ x ∈ U, EqOn (f x) (g x) Ω) :
    MixedPowerBounds p center base loss U Ω H E g := by
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := hf K s
  refine ⟨C, A, hC, hA, ?_⟩
  intro k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  let Jf := J.congr (fun y hy =>
    (mixedDerivative_eq_of_eqOn hΩ (F.spatial y hy) (G.spatial y hy)
      (heq y hy) a b hq).symm)
  exact hb k hk a b hab q hq Jf x hx hlow v hv R hR hhigh hvhigh

end ContinuousFlexibility.Analysis
