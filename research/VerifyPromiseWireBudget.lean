import PEqualNP.Research.PromiseWireBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.PromiseWireBudget

namespace PromiseWireBudgetVerification

-- Four inputs, four gates, one shared intermediate result.
def sharedPorts (j : Fin 4) : List (Fin (4 + 4)) :=
  match j.val with
  | 0 => [0, 1]
  | 1 => [4, 2]
  | 2 => [4, 3]
  | _ => [5, 6]

example : sharing sharedPorts 7 = 1 ∧ arityDeficit sharedPorts = 0 := by decide

example : 4 + 1 = 4 + sharing sharedPorts 7 + arityDeficit sharedPorts :=
  resource_identity sharedPorts 7 (by decide) (by decide) (by decide)

-- Three inputs, three gates: one input is repeated instead of an internal result.
def repeatedInputPorts (j : Fin 3) : List (Fin (3 + 3)) :=
  match j.val with
  | 0 => [0, 1]
  | 1 => [0, 2]
  | _ => [3, 4]

example : sharing repeatedInputPorts 5 = 1 ∧ arityDeficit repeatedInputPorts = 0 := by decide

-- A constant gate contributes two missing operand positions.
def constantPorts (j : Fin 3) : List (Fin (2 + 3)) :=
  match j.val with
  | 0 => []
  | 1 => [0, 2]
  | _ => [3, 1]

example : sharing constantPorts 4 = 0 ∧ arityDeficit constantPorts = 2 := by decide

example : 3 + 1 = 2 + sharing constantPorts 4 + arityDeficit constantPorts :=
  resource_identity constantPorts 4 (by decide) (by decide) (by decide)

-- An unlisted liveness assumption would make the identity false.
def unusedPorts (_ : Fin 1) : List (Fin (3 + 1)) := [0, 1]

example : uses unusedPorts 2 = 0 := by decide
example : 1 + 1 ≠ 3 + sharing unusedPorts 3 + arityDeficit unusedPorts := by decide

-- On the two one-hot rows, NOT of input 1 agrees with input 0 without reading it.
def negatedOther : Circuit := ⟨[⟨.not, [1]⟩], 2⟩

lemma ordered_rows : ImpExcept 0 [true, false] [false, true] := by
  intro index hindex
  cases index with
  | zero => exact (hindex rfl).elim
  | succ index => cases index <;> simp

example : FanInTwo negatedOther := by simp [FanInTwo, negatedOther]
example : ¬ Monotone2 negatedOther := by simp [Monotone2, negatedOther]
example : negatedOther.eval [true, false] = true ∧
    negatedOther.eval [false, true] = false := by decide
example : ¬ (negatedOther.output = 0 ∨
    ∃ gate ∈ negatedOther.gates, 0 ∈ gate.inputs) := by simp [negatedOther]
example : negatedOther.eval [false, false] = true := by decide

-- After unused original coordinates are removed, this NOT circuit has one used input.
def unaryPorts (_ : Fin 1) : List (Fin (1 + 1)) := [0]

example : sharing unaryPorts 1 = 0 ∧ arityDeficit unaryPorts = 1 := by decide
example : sharing unaryPorts 1 + (Finset.univ : Finset (Fin 1)).card ≤ 1 :=
  sharing_unary_budget unaryPorts 1 (by decide) (by decide) (by decide)
    (by decide) Finset.univ (by decide)

example : sharing unaryPorts 1 = 0 ∧ (Finset.univ : Finset (Fin 1)).card = 1 :=
  unary_excludes_sharing unaryPorts 1 (by decide) (by decide) (by decide)
    (by decide) Finset.univ (by decide) (by decide)

-- The weak promise witness above is not an equality witness away from input 0.
example : ¬ EqExcept 0 [true, false] [false, true] := by
  intro h
  have bad := h 1 (by decide)
  cases bad

-- Equality separation also applies to operations outside the AND/OR/NOT basis.
def parityGate : Circuit := ⟨[⟨.mod 2, [0]⟩], 2⟩

lemma equality_rows : EqExcept 0 [false, true] [true, true] := by
  intro index hindex
  cases index with
  | zero => exact (hindex rfl).elim
  | succ index => cases index <;> rfl

example : parityGate.output = 0 ∨ ∃ gate ∈ parityGate.gates, 0 ∈ gate.inputs :=
  equality_separation_forces_read parityGate 0 [false, true] [true, true]
    rfl equality_rows (by decide) (by decide)

end PromiseWireBudgetVerification

#print axioms PEqualNP.Research.PromiseWireBudget.resource_identity
#print axioms PEqualNP.Research.PromiseWireBudget.low_budget_use_le_two
#print axioms PEqualNP.Research.PromiseWireBudget.sharing_unary_budget
#print axioms PEqualNP.Research.PromiseWireBudget.separation_forces_read
#print axioms PEqualNP.Research.PromiseWireBudget.separation_forces_read_or_not

#print axioms PEqualNP.Research.PromiseWireBudget.unary_excludes_sharing

#print axioms PEqualNP.Research.PromiseWireBudget.equality_separation_forces_read
