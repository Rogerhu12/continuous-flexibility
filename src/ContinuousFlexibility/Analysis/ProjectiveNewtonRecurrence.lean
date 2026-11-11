import ContinuousFlexibility.Analysis.ProjectiveNewtonSmoothing

/-!
# A closed low and high grade recurrence for Newton's method

The correction and residual estimates apply to the same smoothed update.
The residual at an intermediate grade is controlled by decomposing it with
the target smoothing operator. The high state grade then controls both tails.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The zeroth jet supplies the high residual bound on a single base ball. -/
theorem exists_zero_tame_bound
    {Z Y : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {a : ℕ → Seminorm ℝ Z} {q : ℕ → Seminorm ℝ Y}
    {U : Set Z} {f : Z → Y} (hT : Statements.SmoothTameOn a q U f)
    {z₀ : Z} (hz₀ : z₀ ∈ U) :
    ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ U, a base (z - z₀) < ε →
          q s (f z) ≤ C * (1 + a (s + loss) z) := by
  obtain ⟨J, hJ⟩ := hT
  obtain ⟨loss, base, ε, hε, H⟩ := hJ 0 z₀ hz₀
  refine ⟨loss, base, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, Hs⟩ := H s hs
  refine ⟨C, hC, ?_⟩
  intro z hz hlow
  have h := Hs z hz hlow Fin.elim0
  simpa only [J.zero z hz, Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero] using h

/-- Decompose a residual with the actual smoothing operator at one scale. -/
theorem seminorm_le_of_smoothing_bounds
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (q : Seminorm ℝ Y) (r Sr : Y) {L H : ℝ}
    (hL : q Sr ≤ L) (hH : q (r - Sr) ≤ H) : q r ≤ L + H := by
  calc
    q r = q (Sr + (r - Sr)) := congrArg (fun x => q x) (by abel)
    _ ≤ q Sr + q (r - Sr) := map_add_le_add q _ _
    _ ≤ L + H := add_le_add hL hH

/-- The state is updated at the original real parameter. -/
def projectiveSmoothedNewtonStep
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X) (S : X →L[ℝ] X) (z : X × ℝ) :
    X × ℝ :=
  (z.1 - S (V z (R z)), z.2)

/-- The same smoothing family and scale sequence are used at every parameter. -/
def projectiveSmoothedNewtonIterates
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X) (S : ℕ → X →L[ℝ] X)
    (N : ℕ → ℕ) (z₀ : X × ℝ) : ℕ → X × ℝ
  | 0 => z₀
  | n + 1 => projectiveSmoothedNewtonStep R V (S (N n))
      (projectiveSmoothedNewtonIterates R V S N z₀ n)

theorem projectiveSmoothedNewtonIterates_parameter
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X) (S : ℕ → X →L[ℝ] X)
    (N : ℕ → ℕ) (z₀ : X × ℝ) (n : ℕ) :
    (projectiveSmoothedNewtonIterates R V S N z₀ n).2 = z₀.2 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- The budget uses just the corrections on the finite prefix. -/
theorem projectiveSmoothedNewtonIterates_displacement_le
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X) (S : ℕ → X →L[ℝ] X)
    (N : ℕ → ℕ) (z₀ : X × ℝ) (p : Seminorm ℝ X) (D : ℕ → ℝ) (n : ℕ) :
    let z := projectiveSmoothedNewtonIterates R V S N z₀
    (∀ k < n, p (S (N k) (V (z k) (R (z k)))) ≤ D k) →
      p ((z n).1 - z₀.1) ≤ ∑ k ∈ Finset.range n, D k := by
  dsimp only
  let z := projectiveSmoothedNewtonIterates R V S N z₀
  induction n with
  | zero =>
      change (∀ k < 0, p (S (N k) (V (z k) (R (z k)))) ≤ D k) →
        p (z₀.1 - z₀.1) ≤ ∑ k ∈ Finset.range 0, D k
      simp
  | succ n ih =>
      intro h
      let d := S (N n) (V (z n) (R (z n)))
      change p (((z n).1 - d) - z₀.1) ≤ ∑ k ∈ Finset.range (n + 1), D k
      rw [show (z n).1 - d - z₀.1 = ((z n).1 - z₀.1) - d by abel, Finset.sum_range_succ]
      exact (map_sub_le_add p _ _).trans
        (add_le_add (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) (h n (Nat.lt_succ_self n)))

private theorem pairGrading_size_step_le
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (n : ℕ) (z : X × ℝ) (d : X) :
    1 + Statements.pairGrading p Statements.realGrading n (z.1 - d, z.2) ≤
      1 + Statements.pairGrading p Statements.realGrading n z + p n d := by
  let t := Statements.realGrading n z.2
  change 1 + (p n (z.1 - d) + t) ≤ 1 + (p n z.1 + t) + p n d
  calc
    _ ≤ 1 + ((p n z.1 + p n d) + t) :=
      add_le_add le_rfl (add_le_add (map_sub_le_add (p n) _ _) le_rfl)
    _ = _ := by ring

private theorem newton_residual_scalar_bound
    {r w X A Dbase Dhigh E C K M G T : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hM : 0 ≤ M) (hG : 1 ≤ G) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hX : 0 ≤ X) (hA : 1 + A ≤ M)
    (hDb : 0 ≤ Dbase) (hDb₁ : Dbase ≤ 1) (hD : Dbase ≤ Dhigh)
    (hprod : Dhigh * Dbase ≤ K ^ 2 * (G * r ^ 2))
    (hE₀ : 0 ≤ E) (hE : E ≤ K * (T * X))
    (hw : w ≤ K * (G * r + T * X)) :
    C * ((1 + A) * r ^ 2 + 2 * (w * r)) + C * (2 + A) * E +
      (C * ((1 + A + Dhigh) * Dbase ^ 2 + 2 * (Dhigh * Dbase))) / 2 ≤
      (C * (M + 2 * K) + C * (M + 3) * K ^ 2 / 2) * (G * r ^ 2) +
        C * (M + 3) * K * (T * X) := by
  have hQ₁ : (1 + A) * r ^ 2 ≤ M * (G * r ^ 2) := by
    apply (mul_le_mul_of_nonneg_right hA (sq_nonneg r)).trans
    apply mul_le_mul_of_nonneg_left _ hM
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hG (sq_nonneg r)
  have hQ₂ : w * r ≤ K * (G * r ^ 2 + T * X) := by
    calc
      _ ≤ (K * (G * r + T * X)) * r := mul_le_mul_of_nonneg_right hw hr
      _ = K * (G * r ^ 2 + (T * X) * r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_of_le_one_right (mul_nonneg hT hX) hr₁)) hK
  have hQ : C * ((1 + A) * r ^ 2 + 2 * (w * r)) ≤
      C * (M * (G * r ^ 2) + 2 * (K * (G * r ^ 2 + T * X))) :=
    mul_le_mul_of_nonneg_left
      (add_le_add hQ₁ (mul_le_mul_of_nonneg_left hQ₂ (by norm_num))) hC
  have hA₁ : 2 + A ≤ M + 1 := by linarith only [hA]
  have hE' : C * (2 + A) * E ≤ C * (M + 1) * (K * (T * X)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA₁ hC) hE hE₀
      (mul_nonneg hC (add_nonneg hM zero_le_one))
  have hDa : 0 ≤ Dhigh := hDb.trans hD
  have hDbSq : Dbase ^ 2 ≤ Dhigh * Dbase := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hD hDb
  have hDbSq₁ : Dbase ^ 2 ≤ Dbase := by
    rw [pow_two]
    exact mul_le_of_le_one_right hDb hDb₁
  have hTay : (1 + A + Dhigh) * Dbase ^ 2 + 2 * (Dhigh * Dbase) ≤
      (M + 3) * (Dhigh * Dbase) := by
    calc
      _ = (1 + A) * Dbase ^ 2 + Dhigh * Dbase ^ 2 + 2 * (Dhigh * Dbase) := by ring
      _ ≤ M * (Dhigh * Dbase) + Dhigh * Dbase + 2 * (Dhigh * Dbase) :=
        add_le_add (add_le_add
          (mul_le_mul hA hDbSq (sq_nonneg _) hM)
          (mul_le_mul_of_nonneg_left hDbSq₁ hDa)) le_rfl
      _ = _ := by ring
  have hTay' := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (hTay.trans (mul_le_mul_of_nonneg_left hprod (add_nonneg hM (by norm_num)))) hC)
    (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    _ ≤ C * (M * (G * r ^ 2) + 2 * (K * (G * r ^ 2 + T * X))) +
        C * (M + 1) * (K * (T * X)) + (C * ((M + 3) * (K ^ 2 * (G * r ^ 2)))) / 2 :=
      add_le_add (add_le_add hQ hE') hTay'
    _ = _ := by ring

private theorem smoothing_bound_of_correction
    {x k g u c v : ℝ} (hk : 0 ≤ k) (hg : 0 ≤ g)
    (hx : x ≤ k * g * u) (hu : u ≤ c * v) :
    x ≤ (k * c) * g * v := by
  calc
    x ≤ k * g * (c * v) := hx.trans (mul_le_mul_of_nonneg_left hu (mul_nonneg hk hg))
    _ = _ := by ring

private theorem exp_mul_nat_mono {a b : ℝ} (h : a ≤ b) (N : ℕ) :
    Real.exp (a * N) ≤ Real.exp (b * N) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg N))

/-- Close the two-grade recurrence for one actual fixed-parameter update.
The low residual is measured at `b+l`; the high state is measured at
`b+h+2*l`. The bounds for the right inverse and the high residual can be
obtained from the homogeneous and zeroth-order tame estimates. -/
theorem projectiveSmoothedNewtonStep_twoGradeRecurrence
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    {R : X × ℝ → ProjectiveLimit F bond} {U : Set (X × ℝ)}
    (J : Statements.SmoothDirections U R) (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    (x₀ : X) (z : X × ℝ) (b₀ b l h σ N : ℕ) (hb₀ : b₀ ≤ b)
    (ε₀ ε C Kₛ Kᵥ M : ℝ) (hC : 0 ≤ C) (hKₛ : 0 ≤ Kₛ) (hKᵥ : 1 ≤ Kᵥ) (hM : 0 ≤ M)
    (hU : {w : X × ℝ | p b₀ (w.1 - x₀) < ε₀ ∧ |w.2| < ε₀} ⊆ U)
    (V : X × ℝ → ProjectiveLimit F bond →ₗ[ℝ] X)
    (Q : X × ℝ → ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (hV : ∀ y, HasProjectiveLineDerivAt (fun x => R (x, z.2))
      (y + Q z (R z) y) z.1 (V z y))
    (SX : X →L[ℝ] X) (SY : ProjectiveLimit F bond →L[ℝ] ProjectiveLimit F bond) :
    let q := gradedSeminorm F bond
    let a := Statements.pairGrading p Statements.realGrading
    let B := b + l
    let A := B + l
    let G := b + h
    let H := b + h + 2 * l
    let r := q B (R z)
    let size := 1 + a H z
    let u := V z (R z)
    let K := Kₛ * Kᵥ
    let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - σ
    let Dbase := K * Real.exp ((σ : ℝ) * N) * r
    let Dhigh := K * Real.exp ((2 * (l : ℝ) + σ) * N) * r
    let _E := K * (Real.exp (-β * N) * size)
    let growth := Real.exp ((2 * (l : ℝ) + 2 * (σ : ℝ)) * N)
    let Cquad := C * (M + 2 * K) + C * (M + 3) * K ^ 2 / 2
    let Ctail := C * (M + 3) * K
    let znext := projectiveSmoothedNewtonStep R V SX z
    (∀ w ∈ U, a b (w - (x₀, 0)) < ε → ∀ d : X × ℝ,
      (q B (projectiveJetHeadLinear J.D 0 w Fin.elim0 d) ≤
        C * ((1 + a A w) * a b d + a A d)) ∧
      (q B (J.D 2 w (Fin.cons d (Fin.cons d Fin.elim0))) ≤
        C * ((1 + a A w) * (a b d) ^ 2 + 2 * (a A d * a b d)))) →
    p b u ≤ Kᵥ * r → p G u ≤ Kᵥ * size → q G (R z) ≤ Kᵥ * size →
    q B (Q z (R z) (R z)) ≤ C * ((1 + a A z) * (q b (R z)) ^ 2 +
      2 * (q A (R z) * q b (R z))) →
    (p b (SX u) ≤ Kₛ * Real.exp ((σ : ℝ) * N) * p b u ∧
      p A (SX u) ≤ Kₛ * Real.exp ((2 * (l : ℝ) + σ) * N) * p b u ∧
      p H (SX u) ≤ Kₛ * Real.exp (((h : ℝ) + 2 * (l : ℝ) + σ) * N) * p b u ∧
      p b (u - SX u) ≤ Kₛ * Real.exp (-β * N) * p G u ∧
      p A (u - SX u) ≤ Kₛ * Real.exp (-β * N) * p G u) →
    (q A (SY (R z)) ≤ Kₛ * Real.exp (((l : ℝ) + σ) * N) * r ∧
      q A (R z - SY (R z)) ≤ Kₛ * Real.exp (-β * N) * q G (R z)) →
    |z.2| < ε₀ → p b (z.1 - x₀) + Dbase < ε₀ → a b (z - (x₀, 0)) + Dbase < ε →
    1 + a A z ≤ M → r ≤ 1 → Dbase ≤ 1 →
    znext ∈ U ∧ znext.2 = z.2 ∧ p A (SX u) ≤ Dhigh ∧
      1 + a H znext ≤ size + K * Real.exp (((h : ℝ) + 2 * (l : ℝ) + σ) * N) * r ∧
      q B (R znext) ≤ (Cquad + Ctail) * (growth * r ^ 2 + Real.exp (-β * N) * size) := by
  dsimp only
  intro hjet hvb hvG hrG hQ hSX hSY hparam hrect hball hA hr₁ hDb₁
  let q := gradedSeminorm F bond
  let a := Statements.pairGrading p Statements.realGrading
  let B := b + l
  let A := B + l
  let H := b + h + 2 * l
  let r := q B (R z)
  let size := 1 + a H z
  let u := V z (R z)
  let K := Kₛ * Kᵥ
  let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - σ
  let Dbase := K * Real.exp ((σ : ℝ) * N) * r
  let Dhigh := K * Real.exp ((2 * (l : ℝ) + σ) * N) * r
  let tail := Real.exp (-β * N)
  let E := K * (tail * size)
  let growth := Real.exp ((2 * (l : ℝ) + 2 * (σ : ℝ)) * N)
  let Cquad := C * (M + 2 * K) + C * (M + 3) * K ^ 2 / 2
  let Ctail := C * (M + 3) * K
  let znext := projectiveSmoothedNewtonStep R V SX z
  have hr : 0 ≤ r := apply_nonneg _ _
  have hsize : 0 ≤ size := add_nonneg zero_le_one (apply_nonneg _ _)
  have hK : 0 ≤ K := mul_nonneg hKₛ (zero_le_one.trans hKᵥ)
  have htail : 0 ≤ tail := (Real.exp_pos _).le
  have hgrowth : 1 ≤ growth := Real.one_le_exp_iff.mpr (by positivity)
  have hDb : 0 ≤ Dbase := mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) hr
  obtain ⟨hXb, hXa, hXH, hXtb, hXta⟩ := hSX
  obtain ⟨hYa, hYt⟩ := hSY
  have hdb : p b (SX u) ≤ Dbase :=
    smoothing_bound_of_correction hKₛ (Real.exp_pos _).le hXb hvb
  have hda : p A (SX u) ≤ Dhigh :=
    smoothing_bound_of_correction hKₛ (Real.exp_pos _).le hXa hvb
  have hdH : p H (SX u) ≤ K * Real.exp (((h : ℝ) + 2 * (l : ℝ) + σ) * N) * r :=
    smoothing_bound_of_correction hKₛ (Real.exp_pos _).le hXH hvb
  have heb : p b (u - SX u) ≤ E := by
    calc
      _ ≤ K * tail * size := smoothing_bound_of_correction hKₛ htail hXtb hvG
      _ = E := mul_assoc K tail size
  have hea : p A (u - SX u) ≤ E := by
    calc
      _ ≤ K * tail * size := smoothing_bound_of_correction hKₛ htail hXta hvG
      _ = E := mul_assoc K tail size
  have hYforward : q A (SY (R z)) ≤ K * (growth * r) := by
    have hr' : r ≤ Kᵥ * r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hKᵥ hr
    have hexp : Real.exp (((l : ℝ) + σ) * N) ≤ growth :=
      exp_mul_nat_mono (by
        linarith only [show (0 : ℝ) ≤ l from Nat.cast_nonneg l,
          show (0 : ℝ) ≤ σ from Nat.cast_nonneg σ]) N
    calc
      _ ≤ K * Real.exp (((l : ℝ) + σ) * N) * r :=
        smoothing_bound_of_correction hKₛ (Real.exp_pos _).le hYa hr'
      _ ≤ K * growth * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hK) hr
      _ = _ := mul_assoc _ _ _
  have hYtail : q A (R z - SY (R z)) ≤ K * (tail * size) := by
    calc
      _ ≤ K * tail * size := smoothing_bound_of_correction hKₛ htail hYt hrG
      _ = _ := mul_assoc _ _ _
  have hw : q A (R z) ≤ K * (growth * r + tail * size) := by
    calc
      _ ≤ K * (growth * r) + K * (tail * size) :=
        seminorm_le_of_smoothing_bounds (q A) (R z) (SY (R z)) hYforward hYtail
      _ = _ := by ring
  have hqr : q b (R z) ≤ r := gradedSeminorm_monotone F bond (Nat.le_add_right b l) _
  have hA₀ : 0 ≤ 1 + a A z := add_nonneg zero_le_one (apply_nonneg _ _)
  have hQ' : q B (Q z (R z) (R z)) ≤ C * ((1 + a A z) * r ^ 2 + 2 * (q A (R z) * r)) :=
    hQ.trans (mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (apply_nonneg _ _) hqr 2) hA₀)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqr (apply_nonneg _ _))
          (by norm_num))) hC)
  have hD : Dbase ≤ Dhigh := by
    have hexp : Real.exp ((σ : ℝ) * N) ≤ Real.exp ((2 * (l : ℝ) + σ) * N) :=
      exp_mul_nat_mono (by linarith only [show (0 : ℝ) ≤ l from Nat.cast_nonneg l]) N
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hK) hr
  have hprod : Dhigh * Dbase = K ^ 2 * (growth * r ^ 2) := by
    have harg : (2 * (l : ℝ) + σ) * N + (σ : ℝ) * N =
        (2 * (l : ℝ) + 2 * (σ : ℝ)) * N := by ring
    calc
      _ = K ^ 2 * ((Real.exp ((2 * (l : ℝ) + σ) * N) * Real.exp ((σ : ℝ) * N)) * r ^ 2) := by
        dsimp only [Dhigh, Dbase]
        ring
      _ = _ := by rw [← Real.exp_add, harg]
  have hstep := projectiveSmoothedNewtonStep_residual_le_of_bounds J p hp x₀ z b₀ b l B hb₀
    ε₀ ε C hC hU (V z) (Q z) hV SX Dbase Dhigh E _ hjet hdb hda heb hea hparam hrect hball hQ'
  have hrnext : q B (R znext) ≤ Cquad * (growth * r ^ 2) + Ctail * (tail * size) :=
    hstep.trans (newton_residual_scalar_bound hC hK hM hgrowth htail hr hr₁ hsize hA
      hDb hDb₁ hD hprod.le (mul_nonneg hK (mul_nonneg htail hsize)) le_rfl hw)
  have hm : p b₀ (z.1 - x₀) + p b₀ (SX u) < ε₀ :=
    (add_le_add (hp hb₀ _) ((hp hb₀ _).trans hdb)).trans_lt hrect
  have hznext : znext ∈ U := by
    have hend := newton_segment_mem_of_seminorm_margin (p b₀) x₀ z (SX u) hparam hm 1
      ⟨zero_le_one, le_rfl⟩
    have he : z + (1 : ℝ) • ((-SX u, 0) : X × ℝ) = znext := by
      rw [one_smul]
      change (z.1 + -SX u, z.2 + (0 : ℝ)) = (z.1 - SX u, z.2)
      rw [sub_eq_add_neg, add_zero]
    rw [he] at hend
    exact hU hend
  have hQnonneg : 0 ≤ Cquad := by dsimp only [Cquad]; positivity
  have hTnonneg : 0 ≤ Ctail := by dsimp only [Ctail]; positivity
  have hGR : 0 ≤ growth * r ^ 2 := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hTX : 0 ≤ tail * size := mul_nonneg htail hsize
  refine ⟨hznext, rfl, hda, (pairGrading_size_step_le p H z (SX u)).trans
    (add_le_add le_rfl hdH), ?_⟩
  calc
    _ ≤ Cquad * (growth * r ^ 2) + Ctail * (tail * size) := hrnext
    _ ≤ (Cquad + Ctail) * (growth * r ^ 2) + (Cquad + Ctail) * (tail * size) :=
      add_le_add
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hTnonneg) hGR)
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hQnonneg) hTX)
    _ = _ := by ring

/-- The homogeneous right inverse and the zeroth-order residual estimate
bound all three quantities needed by the closed recurrence. The constant
uses only the finite-grade tame constant and the low state bound. -/
theorem newton_correction_bounds_of_tame
    {Z X Y : Type*} [AddCommGroup Z] [Module ℝ Z]
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (a : ℕ → Seminorm ℝ Z) (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (ha : Monotone a) (hq : Monotone q) (z : Z) (u : X) (r : Y)
    (b l h : ℕ) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hA : 1 + a (b + l + l) z ≤ M) (hr : q (b + l) r ≤ 1)
    (hVb : p b u ≤ C * (q (b + l) r + (1 + a (b + l) z) * q b r))
    (hVg : p (b + h) u ≤ C * (q (b + h + l) r + (1 + a (b + h + l) z) * q b r))
    (hRg : q (b + h + l) r ≤ C * (1 + a (b + h + 2 * l) z)) :
    let K := 1 + C + C * (M + 1) + C * (C + 1)
    let size := 1 + a (b + h + 2 * l) z
    1 ≤ K ∧ p b u ≤ K * q (b + l) r ∧
      p (b + h) u ≤ K * size ∧ q (b + h) r ≤ K * size := by
  dsimp only
  let K := 1 + C + C * (M + 1) + C * (C + 1)
  let size := 1 + a (b + h + 2 * l) z
  have hC₁ : 0 ≤ C * (M + 1) := by positivity
  have hC₂ : 0 ≤ C * (C + 1) := by positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith only [hC, hC₁, hC₂]
  have hKb : C * (M + 1) ≤ K := by dsimp only [K]; linarith only [hC, hC₂]
  have hKg : C * (C + 1) ≤ K := by dsimp only [K]; linarith only [hC, hC₁]
  have hKC : C ≤ K := by dsimp only [K]; linarith only [hC₁, hC₂]
  have hqbase : q b r ≤ q (b + l) r := hq (Nat.le_add_right b l) r
  have hAb : 1 + a (b + l) z ≤ M :=
    (add_le_add le_rfl (ha (Nat.le_add_right (b + l) l) z)).trans hA
  have hsize : 0 ≤ size := add_nonneg zero_le_one (apply_nonneg _ _)
  have hAs : 1 + a (b + h + l) z ≤ size :=
    add_le_add le_rfl (ha (by omega) z)
  refine ⟨hK, ?_, ?_, ?_⟩
  · calc
      _ ≤ C * (q (b + l) r + M * q (b + l) r) :=
        hVb.trans (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul hAb hqbase (apply_nonneg _ _) hM)) hC)
      _ = C * (M + 1) * q (b + l) r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKb (apply_nonneg _ _)
  · have hh : (1 + a (b + h + l) z) * q b r ≤ size := by
      simpa only [mul_one] using
        mul_le_mul hAs (hqbase.trans hr) (apply_nonneg _ _) hsize
    calc
      _ ≤ C * (C * size + size) :=
        hVg.trans (mul_le_mul_of_nonneg_left (add_le_add hRg hh) hC)
      _ = C * (C + 1) * size := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKg hsize
  · exact (hq (Nat.le_add_right (b + h) l) r).trans
      (hRg.trans (mul_le_mul_of_nonneg_right hKC hsize))

private theorem weaken_smoothing_exponent
    {x c K a b u : ℝ} {N : ℕ}
    (h : x ≤ c * Real.exp (a * N) * u) (hc : c ≤ K) (hK : 0 ≤ K)
    (hab : a ≤ b) (hu : 0 ≤ u) : x ≤ K * Real.exp (b * N) * u :=
  h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hc (exp_mul_nat_mono hab N) (Real.exp_pos _).le hK) hu)

/-- Extract both actual smoothing families once. A common base and loss
give all the forward and tail bounds at the grades of the recurrence. -/
theorem exists_twoGradeNewtonSmoothingBounds
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    (hX : Statements.HasSmoothing p) (hY : Statements.HasSmoothing q) :
    ∃ base loss : ℕ, ∃ SX : ℕ → X →L[ℝ] X, ∃ SY : ℕ → Y →L[ℝ] Y,
      (∀ u, Tendsto (fun N => SX N u) atTop (𝓝 u)) ∧
      (∀ r, Tendsto (fun N => SY N r) atTop (𝓝 r)) ∧
      ∀ b l h : ℕ, base ≤ b → 2 * l ≤ h →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (u : X) (r : Y),
          let B := b + l
          let A := B + l
          let G := b + h
          let H := b + h + 2 * l
          let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - loss
          (p b (SX N u) ≤ K * Real.exp ((loss : ℝ) * N) * p b u ∧
            p A (SX N u) ≤ K * Real.exp ((2 * (l : ℝ) + loss) * N) * p b u ∧
            p H (SX N u) ≤ K * Real.exp (((h : ℝ) + 2 * (l : ℝ) + loss) * N) * p b u ∧
            p b (u - SX N u) ≤ K * Real.exp (-β * N) * p G u ∧
            p A (u - SX N u) ≤ K * Real.exp (-β * N) * p G u) ∧
          (q A (SY N r) ≤ K * Real.exp (((l : ℝ) + loss) * N) * q B r ∧
            q A (r - SY N r) ≤ K * Real.exp (-β * N) * q G r) := by
  obtain ⟨bX, lX, SX, FX, TX, limX⟩ := hX
  obtain ⟨bY, lY, SY, FY, TY, limY⟩ := hY
  let loss := max lX lY
  let base := max bX bY
  refine ⟨base, loss, SX, SY, limX, limY, ?_⟩
  intro b l h hb hl
  let B := b + l
  let A := B + l
  let G := b + h
  let H := b + h + 2 * l
  let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - loss
  have hbX : bX ≤ b := (le_max_left bX bY).trans hb
  have hbY : bY ≤ b := (le_max_right bX bY).trans hb
  have hBA : B ≤ A := Nat.le_add_right _ _
  have hbB : b ≤ B := Nat.le_add_right _ _
  have hbA : b ≤ A := hbB.trans hBA
  have hbH : b ≤ H := by dsimp only [H]; omega
  have hAG : A ≤ G := by dsimp only [A, B, G]; omega
  obtain ⟨Cx₁, hx₁, fx₁⟩ := FX b b hbX le_rfl
  obtain ⟨Cx₂, hx₂, fx₂⟩ := FX b A hbX hbA
  obtain ⟨Cx₃, hx₃, fx₃⟩ := FX b H hbX hbH
  obtain ⟨Cx₄, hx₄, tx₄⟩ := TX b G hbX (hbA.trans hAG)
  obtain ⟨Cx₅, hx₅, tx₅⟩ := TX A G (hbX.trans hbA) hAG
  obtain ⟨Cy₁, hy₁, fy₁⟩ := FY B A (hbY.trans hbB) hBA
  obtain ⟨Cy₂, hy₂, ty₂⟩ := TY A G (hbY.trans hbA) hAG
  let K := Cx₁ + Cx₂ + Cx₃ + Cx₄ + Cx₅ + Cy₁ + Cy₂
  have hK : 0 ≤ K := by dsimp only [K]; linarith only [hx₁, hx₂, hx₃, hx₄, hx₅, hy₁, hy₂]
  have hlX : (lX : ℝ) ≤ loss := by exact_mod_cast (le_max_left lX lY)
  have hlY : (lY : ℝ) ≤ loss := by exact_mod_cast (le_max_right lX lY)
  have hl₀ : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have e₁ : (b : ℝ) - b + lX ≤ loss := by linarith only [hlX]
  have e₂ : (A : ℝ) - b + lX ≤ 2 * (l : ℝ) + loss := by
    simp only [A, B, Nat.cast_add]
    linarith only [hlX]
  have e₃ : (H : ℝ) - b + lX ≤ (h : ℝ) + 2 * (l : ℝ) + loss := by
    simp only [H, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hlX]
  have e₄ : -((G : ℝ) - b - lX) ≤ -β := by
    simp only [G, β, Nat.cast_add]
    linarith only [hlX, hl₀]
  have e₅ : -((G : ℝ) - A - lX) ≤ -β := by
    simp only [G, A, B, β, Nat.cast_add]
    linarith only [hlX]
  have e₆ : (A : ℝ) - B + lY ≤ (l : ℝ) + loss := by
    simp only [A, Nat.cast_add]
    linarith only [hlY]
  have e₇ : -((G : ℝ) - A - lY) ≤ -β := by
    simp only [G, A, B, β, Nat.cast_add]
    linarith only [hlY]
  refine ⟨K, hK, ?_⟩
  intro N u r
  have hCx₁ : Cx₁ ≤ K := by dsimp only [K]; linarith only [hx₂, hx₃, hx₄, hx₅, hy₁, hy₂]
  have hCx₂ : Cx₂ ≤ K := by dsimp only [K]; linarith only [hx₁, hx₃, hx₄, hx₅, hy₁, hy₂]
  have hCx₃ : Cx₃ ≤ K := by dsimp only [K]; linarith only [hx₁, hx₂, hx₄, hx₅, hy₁, hy₂]
  have hCx₄ : Cx₄ ≤ K := by dsimp only [K]; linarith only [hx₁, hx₂, hx₃, hx₅, hy₁, hy₂]
  have hCx₅ : Cx₅ ≤ K := by dsimp only [K]; linarith only [hx₁, hx₂, hx₃, hx₄, hy₁, hy₂]
  have hCy₁ : Cy₁ ≤ K := by dsimp only [K]; linarith only [hx₁, hx₂, hx₃, hx₄, hx₅, hy₂]
  have hCy₂ : Cy₂ ≤ K := by dsimp only [K]; linarith only [hx₁, hx₂, hx₃, hx₄, hx₅, hy₁]
  exact ⟨⟨weaken_smoothing_exponent (fx₁ N u) hCx₁ hK e₁ (apply_nonneg _ _),
      weaken_smoothing_exponent (fx₂ N u) hCx₂ hK e₂ (apply_nonneg _ _),
      weaken_smoothing_exponent (fx₃ N u) hCx₃ hK e₃ (apply_nonneg _ _),
      weaken_smoothing_exponent (tx₄ N u) hCx₄ hK e₄ (apply_nonneg _ _),
      weaken_smoothing_exponent (tx₅ N u) hCx₅ hK e₅ (apply_nonneg _ _)⟩,
    ⟨weaken_smoothing_exponent (fy₁ N r) hCy₁ hK e₆ (apply_nonneg _ _),
      weaken_smoothing_exponent (ty₂ N r) hCy₂ hK e₇ (apply_nonneg _ _)⟩⟩

end ContinuousFlexibility.Analysis
