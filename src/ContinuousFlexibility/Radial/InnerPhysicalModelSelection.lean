import ContinuousFlexibility.Radial.InnerPhysicalOrderedChoices

/-!
# Selecting the one physical model used by the actual dictionary

The selectors use the already proved ordered families. Their public
properties refer to the selected model itself, so a later chain cannot
use one witness for the equation and another for the estimates. The
Morse selector is shared by the two tails and normalizes the even
natural frequency to the same real expression as the central chart.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements
open scoped Matrix.Norms.L2Operator

section Central

variable {C K X₀ η : ℝ} (hfamily : InnerCentralPhysicalFamily C K X₀ η)
  (q : ℕ) (hq : 1 ≤ q)

def innerSelectedCentralModel : InnerBufferLocalizedData (innerCentralBufferData q X₀) C K :=
  Classical.choose (hfamily.2 q hq).2

theorem innerSelectedCentralModel_hypotheses : BufferHypotheses (innerCentralBufferData q X₀) :=
  (hfamily.2 q hq).1

theorem innerSelectedCentralModel_cutEnergy_pos (i : Fin 2) :
    0 < innerCentralModelCutEnergy (innerSelectedCentralModel hfamily q hq) i :=
  (Classical.choose_spec (hfamily.2 q hq).2).1 i

theorem innerSelectedCentralModel_poisson_bound :
    InnerCentralPhysicalPoissonBound (innerSelectedCentralModel hfamily q hq) :=
  (Classical.choose_spec (hfamily.2 q hq).2).2.1

theorem innerSelectedCentralModel_error {height : ℝ} (hh : 0 < height) (sign : Bool) :
    ‖innerTwoCutWeightedError
      (innerPhysicalCutKappa height
        (fun i => centralDensityRoot (bufferCut (innerCentralBufferData q X₀) i))
        (innerCentralModelCutEnergy (innerSelectedCentralModel hfamily q hq))) (fun _ => 1)
      ((innerSelectedCentralModel hfamily q hq).physicalFluxError height
        (fun i => centralDensityRoot (bufferCut (innerCentralBufferData q X₀) i))) sign‖ < η :=
  (Classical.choose_spec (hfamily.2 q hq).2).2.2 height hh sign

end Central

section Morse

variable {a Cstar C K η : ℝ} {N : ℕ}
  (hfamily : InnerMorsePhysicalFamily a Cstar N C K η)
  {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {cost : ℕ → ℝ}
  (hreal : MorseChainRealization T σ D cost) (hindex : T.index = N)
  (m n q : ℕ) (hm : N ≤ m) (hmn : m < n) (hq : 1 ≤ q)
  (hband : radialFrequencyBand T Cstar n (2 * q))

theorem innerMorsePhysicalFamily_even :
    BufferHypotheses
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) ((2 : ℝ) * q)
        (8 * (T.d m : ℝ) ^ 9)) ∧
    ∃ M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) ((2 : ℝ) * q)
        (8 * (T.d m : ℝ) ^ 9)) C K,
      (∀ i, 0 < (M.column i).inwardEnergy) ∧
      InnerMorsePhysicalPoissonBound hreal N a M ∧
      ∀ γ : ℝ, |γ| ≤ 1 → ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
        ‖innerTwoCutWeightedError
          (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
          (innerMorseCutWeight N a γ side m)
          (M.physicalFluxError height (fun _ => 1)) sign‖ < η := by
  have hj : 2 ≤ 2 * q := by omega
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    hfamily T σ D cost hreal hindex m n (2 * q) hm hmn hj hband

def innerSelectedMorseModel : InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA T m) (morseChainB T m) ((2 : ℝ) * q)
      (8 * (T.d m : ℝ) ^ 9)) C K :=
  Classical.choose (innerMorsePhysicalFamily_even hfamily hreal hindex m n q hm hmn hq hband).2

theorem innerSelectedMorseModel_hypotheses :
    BufferHypotheses
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) ((2 : ℝ) * q)
        (8 * (T.d m : ℝ) ^ 9)) :=
  (innerMorsePhysicalFamily_even hfamily hreal hindex m n q hm hmn hq hband).1

theorem innerSelectedMorseModel_energy_pos (i : Fin 2) :
    0 < ((innerSelectedMorseModel hfamily hreal hindex m n q hm hmn hq hband).column i).inwardEnergy :=
  (Classical.choose_spec
    (innerMorsePhysicalFamily_even hfamily hreal hindex m n q hm hmn hq hband).2).1 i

theorem innerSelectedMorseModel_poisson_bound :
    InnerMorsePhysicalPoissonBound hreal N a
      (innerSelectedMorseModel hfamily hreal hindex m n q hm hmn hq hband) :=
  (Classical.choose_spec
    (innerMorsePhysicalFamily_even hfamily hreal hindex m n q hm hmn hq hband).2).2.1

theorem innerSelectedMorseModel_error {γ : ℝ} (hγ : |γ| ≤ 1) (side : Bool)
    {height : ℝ} (hh : 0 < height) (sign : Bool) :
    ‖innerTwoCutWeightedError
      (innerPhysicalCutKappa height (fun _ => 1)
        (fun i =>
          ((innerSelectedMorseModel hfamily hreal hindex m n q hm hmn hq hband).column i).inwardEnergy))
      (innerMorseCutWeight N a γ side m)
      ((innerSelectedMorseModel hfamily hreal hindex m n q hm hmn hq hband).physicalFluxError
        height (fun _ => 1)) sign‖ < η :=
  (Classical.choose_spec
    (innerMorsePhysicalFamily_even hfamily hreal hindex m n q hm hmn hq hband).2).2.2
      γ hγ side height hh sign

end Morse

end ContinuousFlexibility.Radial
