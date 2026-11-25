import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs.MetaComplexityLgpMono

/-!
A resource identity for finite wirings and a separation principle for promise rows.

The wiring identity is independent of gate semantics. Its liveness hypotheses are
explicit: the output has no reader, and every other listed wire has a reader.
It does not assert that an arbitrary circuit is already normalized or live.
-/

namespace PEqualNP.Research.PromiseWireBudget

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Accounting

variable {inputs gates : ℕ}

/-- Repeated operand positions count as separate uses. -/
def uses (ports : Fin gates → List (Fin (inputs + gates))) (wire : Fin (inputs + gates)) : ℕ :=
  ∑ gate, (ports gate).count wire

/-- Uses beyond the first, excluding the output wire. -/
def sharing (ports : Fin gates → List (Fin (inputs + gates)))
    (output : Fin (inputs + gates)) : ℕ :=
  ∑ wire, if wire = output then 0 else uses ports wire - 1

/-- Unfilled binary operand positions; unary gates cost one, constants two. -/
def arityDeficit (ports : Fin gates → List (Fin (inputs + gates))) : ℕ :=
  ∑ gate : Fin gates, (2 - (ports gate).length)

lemma sum_count {size : ℕ} (xs : List (Fin size)) :
    (∑ wire : Fin size, xs.count wire) = xs.length := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.count_cons, Finset.sum_add_distrib, ih]

lemma use_balance (ports : Fin gates → List (Fin (inputs + gates))) :
    (∑ wire, uses ports wire) = ∑ gate, (ports gate).length := by
  unfold uses
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun gate _ => sum_count (ports gate))

/-- The extra gates above a binary tree pay exactly for sharing and arity deficits. -/
theorem resource_identity (ports : Fin gates → List (Fin (inputs + gates)))
    (output : Fin (inputs + gates))
    (binary : ∀ gate, (ports gate).length ≤ 2)
    (output_unused : uses ports output = 0)
    (live : ∀ wire, wire ≠ output → 1 ≤ uses ports wire) :
    gates + 1 = inputs + sharing ports output + arityDeficit ports := by
  classical
  have per_wire (wire : Fin (inputs + gates)) :
      uses ports wire + (if wire = output then 1 else 0) =
        (if wire = output then 0 else uses ports wire - 1) + 1 := by
    by_cases h : wire = output
    · subst wire
      simp [output_unused]
    · have huse := live wire h
      simp only [h, ↓reduceIte]
      omega
  have wire_sum : (∑ wire, uses ports wire) + 1 = sharing ports output + (inputs + gates) := by
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun wire _ => per_wire wire)
    simpa [Finset.sum_add_distrib, sharing] using h
  have arity_sum : (∑ gate, (ports gate).length) + arityDeficit ports = 2 * gates := by
    have h : ∀ gate, (ports gate).length + (2 - (ports gate).length) = 2 := by
      intro gate
      have hb := binary gate
      omega
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun gate _ => h gate)
    simpa [Finset.sum_add_distrib, arityDeficit, Nat.mul_comm] using hs
  have balance := use_balance ports
  omega

/-- A circuit with no more gates than listed inputs has at most one unit of slack. -/
theorem low_budget (ports : Fin gates → List (Fin (inputs + gates)))
    (output : Fin (inputs + gates))
    (binary : ∀ gate, (ports gate).length ≤ 2)
    (output_unused : uses ports output = 0)
    (live : ∀ wire, wire ≠ output → 1 ≤ uses ports wire)
    (budget : gates ≤ inputs) : sharing ports output + arityDeficit ports ≤ 1 := by
  have h := resource_identity ports output binary output_unused live
  omega

/-- In the low-budget regime no wire can be read three times. -/
theorem low_budget_use_le_two (ports : Fin gates → List (Fin (inputs + gates)))
    (output : Fin (inputs + gates))
    (binary : ∀ gate, (ports gate).length ≤ 2)
    (output_unused : uses ports output = 0)
    (live : ∀ wire, wire ≠ output → 1 ≤ uses ports wire)
    (budget : gates ≤ inputs) (wire : Fin (inputs + gates)) : uses ports wire ≤ 2 := by
  classical
  by_cases ho : wire = output
  · subst wire
    omega
  have hterm : uses ports wire - 1 ≤ sharing ports output := by
    have h := Finset.single_le_sum (f := fun w => if w = output then 0 else uses ports w - 1)
      (fun w _ => Nat.zero_le _) (Finset.mem_univ wire)
    simpa [sharing, ho] using h
  have hb := low_budget ports output binary output_unused live budget
  omega

/-- Any specified set of unary or constant gates is paid for by the deficit. -/
theorem unary_charge (ports : Fin gates → List (Fin (inputs + gates)))
    (charged : Finset (Fin gates))
    (unary : ∀ gate ∈ charged, (ports gate).length ≤ 1) :
    charged.card ≤ arityDeficit ports := by
  classical
  have point (gate : Fin gates) :
      (if gate ∈ charged then 1 else 0) ≤ 2 - (ports gate).length := by
    by_cases h : gate ∈ charged
    · have hu := unary gate h
      simp only [h, ↓reduceIte]
      omega
    · simp [h]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun gate _ => point gate)
  simpa [arityDeficit] using h

/-- Sharing and normalized unary gates draw from the same low-budget allowance. -/
theorem sharing_unary_budget (ports : Fin gates → List (Fin (inputs + gates)))
    (output : Fin (inputs + gates))
    (binary : ∀ gate, (ports gate).length ≤ 2)
    (output_unused : uses ports output = 0)
    (live : ∀ wire, wire ≠ output → 1 ≤ uses ports wire)
    (budget : gates ≤ inputs) (charged : Finset (Fin gates))
    (unary : ∀ gate ∈ charged, (ports gate).length ≤ 1) :
    sharing ports output + charged.card ≤ 1 := by
  have hb := low_budget ports output binary output_unused live budget
  have hc := unary_charge ports charged unary
  omega

/-- One charged unary gate leaves no budget for repeated wire uses. -/
theorem unary_excludes_sharing (ports : Fin gates → List (Fin (inputs + gates)))
    (output : Fin (inputs + gates))
    (binary : ∀ gate, (ports gate).length ≤ 2)
    (output_unused : uses ports output = 0)
    (live : ∀ wire, wire ≠ output → 1 ≤ uses ports wire)
    (budget : gates ≤ inputs) (charged : Finset (Fin gates))
    (unary : ∀ gate ∈ charged, (ports gate).length ≤ 1) (exists_unary : charged.Nonempty) :
    sharing ports output = 0 ∧ charged.card = 1 := by
  have hb := sharing_unary_budget ports output binary output_unused live budget charged unary
  have hp := Finset.card_pos.mpr exists_unary
  omega

end Accounting

section Separation

/-- Row comparison after one distinguished coordinate is ignored. -/
def ImpExcept (ignored : ℕ) (xs ys : List Bool) : Prop :=
  ∀ index, index ≠ ignored → xs.getD index false = true → ys.getD index false = true

def gateEval (xs : List Bool) (gate : Gate) : Bool :=
  gate.op.eval (gate.inputs.map fun index => xs.getD index false)

def run (gates : List Gate) (xs : List Bool) : List Bool :=
  gates.foldl (fun ws gate => ws ++ [gateEval ws gate]) xs

lemma getD_snoc (xs : List Bool) (value : Bool) (index : ℕ) :
    (xs ++ [value]).getD index false =
      if index = xs.length then value else xs.getD index false := by
  rcases lt_trichotomy index xs.length with h | h | h
  · have hn : index ≠ xs.length := by omega
    simp only [hn, ↓reduceIte]
    exact List.getD_append _ _ _ _ h
  · subst index
    simp
  · have hn : index ≠ xs.length := by omega
    simp only [hn, ↓reduceIte]
    rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma append_imp {ignored : ℕ} {xs ys : List Bool} {a b : Bool}
    (same_length : xs.length = ys.length) (before : ImpExcept ignored xs ys)
    (new_value : a = true → b = true) :
    ImpExcept ignored (xs ++ [a]) (ys ++ [b]) := by
  intro index hindex
  rw [getD_snoc, getD_snoc, ← same_length]
  by_cases h : index = xs.length
  · simpa [h] using new_value
  · simpa [h] using before index hindex

lemma monotone_gate {ignored : ℕ} {xs ys : List Bool} (gate : Gate)
    (allowed : gate.op = .and ∨ gate.op = .or)
    (no_read : ignored ∉ gate.inputs) (ordered : ImpExcept ignored xs ys) :
    gateEval xs gate = true → gateEval ys gate = true := by
  have point (index : ℕ) (hindex : index ∈ gate.inputs) :
      xs.getD index false = true → ys.getD index false = true :=
    ordered index (fun h => no_read (h ▸ hindex))
  rcases allowed with h | h
  · simp only [gateEval, h, GateOp.eval, List.all_eq_true, List.mem_map]
    intro hx value hv
    obtain ⟨index, hindex, rfl⟩ := hv
    exact point index hindex (hx _ ⟨index, hindex, rfl⟩)
  · simp only [gateEval, h, GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨value, ⟨index, hindex, rfl⟩, hvalue⟩
    exact ⟨_, ⟨index, hindex, rfl⟩, point index hindex hvalue⟩

lemma run_imp_except (gates : List Gate) {ignored : ℕ} {xs ys : List Bool}
    (allowed : ∀ gate ∈ gates, gate.op = .and ∨ gate.op = .or)
    (no_read : ∀ gate ∈ gates, ignored ∉ gate.inputs)
    (same_length : xs.length = ys.length) (ordered : ImpExcept ignored xs ys) :
    ImpExcept ignored (run gates xs) (run gates ys) := by
  induction gates generalizing xs ys with
  | nil => exact ordered
  | cons gate gates ih =>
    apply ih (fun g hg => allowed g (List.mem_cons_of_mem _ hg))
      (fun g hg => no_read g (List.mem_cons_of_mem _ hg))
    · simpa using same_length
    · exact append_imp same_length ordered
        (monotone_gate gate (allowed gate List.mem_cons_self)
          (no_read gate List.mem_cons_self) ordered)

/-- Equality witnesses are stronger than row-order witnesses and need no gate-basis restriction. -/
def EqExcept (ignored : ℕ) (xs ys : List Bool) : Prop :=
  ∀ index, index ≠ ignored → xs.getD index false = ys.getD index false

lemma run_eq_except (gates : List Gate) {ignored : ℕ} {xs ys : List Bool}
    (no_read : ∀ gate ∈ gates, ignored ∉ gate.inputs)
    (same_length : xs.length = ys.length) (equal : EqExcept ignored xs ys) :
    EqExcept ignored (run gates xs) (run gates ys) := by
  induction gates generalizing xs ys with
  | nil => exact equal
  | cons gate gates ih =>
    have gate_equal : gateEval xs gate = gateEval ys gate := by
      unfold gateEval
      congr 1
      apply List.map_congr_left
      intro index hindex
      exact equal index (fun h => no_read gate List.mem_cons_self (h ▸ hindex))
    apply ih (fun g hg => no_read g (List.mem_cons_of_mem _ hg))
    · simpa using same_length
    · intro index hindex
      rw [getD_snoc, getD_snoc, ← same_length]
      by_cases h : index = xs.length
      · simpa [h] using gate_equal
      · simpa [h] using equal index hindex

/-- A Hamming-style separating pair forces a read for every operation in the root circuit type. -/
theorem equality_separation_forces_read (C : Circuit) (ignored : ℕ) (xs ys : List Bool)
    (same_length : xs.length = ys.length) (equal : EqExcept ignored xs ys)
    (positive : C.eval xs = true) (negative : C.eval ys = false) :
    C.output = ignored ∨ ∃ gate ∈ C.gates, ignored ∈ gate.inputs := by
  classical
  by_contra h
  have hout : C.output ≠ ignored := fun ho => h (Or.inl ho)
  have no_read : ∀ gate ∈ C.gates, ignored ∉ gate.inputs := by
    intro gate hgate hread
    exact h (Or.inr ⟨gate, hgate, hread⟩)
  have result := run_eq_except C.gates no_read same_length equal C.output hout
  change C.eval xs = C.eval ys at result
  rw [positive, negative] at result
  cases result

/-- A promised positive/negative row pair forces a read or the distinguished output. -/
theorem separation_forces_read (C : Circuit) (ignored : ℕ) (xs ys : List Bool)
    (monotone : Monotone2 C) (same_length : xs.length = ys.length)
    (ordered : ImpExcept ignored xs ys)
    (positive : C.eval xs = true) (negative : C.eval ys = false) :
    C.output = ignored ∨ ∃ gate ∈ C.gates, ignored ∈ gate.inputs := by
  classical
  by_contra h
  have hout : C.output ≠ ignored := fun ho => h (Or.inl ho)
  have no_read : ∀ gate ∈ C.gates, ignored ∉ gate.inputs := by
    intro gate hgate hread
    exact h (Or.inr ⟨gate, hgate, hread⟩)
  have allowed : ∀ gate ∈ C.gates, gate.op = .and ∨ gate.op = .or := by
    intro gate hgate
    exact (monotone gate hgate).1
  have step := run_imp_except C.gates allowed no_read same_length ordered C.output hout
  change C.eval xs = true → C.eval ys = true at step
  have bad := step positive
  rw [negative] at bad
  cases bad

/-- The corresponding statement for the full basis has an explicit NOT alternative. -/
theorem separation_forces_read_or_not (C : Circuit) (ignored : ℕ) (xs ys : List Bool)
    (binary_basis : FanInTwo C) (same_length : xs.length = ys.length)
    (ordered : ImpExcept ignored xs ys)
    (positive : C.eval xs = true) (negative : C.eval ys = false) :
    (C.output = ignored ∨ ∃ gate ∈ C.gates, ignored ∈ gate.inputs) ∨
      ∃ gate ∈ C.gates, gate.op = .not := by
  classical
  by_cases hnot : ∃ gate ∈ C.gates, gate.op = .not
  · exact Or.inr hnot
  · apply Or.inl
    apply separation_forces_read C ignored xs ys ?_ same_length ordered positive negative
    intro gate hgate
    obtain ⟨hop, hlen⟩ := binary_basis gate hgate
    refine ⟨?_, hlen⟩
    change gate.op = GateOp.and ∨ gate.op = GateOp.or ∨ gate.op = GateOp.not at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨gate, hgate, h⟩).elim

end Separation

end PEqualNP.Research.PromiseWireBudget
