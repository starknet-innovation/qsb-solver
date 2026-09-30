import QSB.PinningShape
import QSB.ByteFinalCounts

/-!
For a bare output, model the boundary between scriptSig and the locking script
by an arbitrary partial evaluator that returns the former's final byte stack.
The generated lock starts from that stack with its own opcode counter. No
push-only or canonical witness-shape premise is imposed on the evaluator.

This is composition *inside the byte model*. In particular it does not prove
that Core's EvalScript for the lock is simulated by `ByteMachine.run`, that
the Boolean signature outcomes agree with Core, or that Core accepts the
transaction whenever this model does.
-/
namespace QSB.BareBoundary
open ByteMachine

def evalBare {σ : Type*} (evalScriptSig : σ → Option (List Bytes))
    (hashes : Hashes) (outcomes : List Bool) (scriptSig : σ) : Option State := do
  let stack ← evalScriptSig scriptSig
  run hashes ByteLayout.program (State.mk stack outcomes 0)

/-- Whatever program produced the initial stack, successful modeled execution
of the bare lock forces the first signed opening to match a lock-owned HORS
commitment. An actual Core-to-byte-model refinement is still required. -/
theorem accepted_bare_composition_first_origin {σ : Type*}
    (evalScriptSig : σ → Option (List Bytes)) (hashes : Hashes)
    (outcomes : List Bool) (scriptSig : σ) (final : State)
    (accepted : evalBare evalScriptSig hashes outcomes scriptSig = some final) :
    ∃ stack, evalScriptSig scriptSig = some stack ∧
      ∃ nonce puzzle raw tail later,
        stack = nonce :: puzzle :: raw :: tail ∧
        outcomes = true :: true :: later ∧
        ∃ i : Fin 150, ∃ opening : Bytes,
          ByteIndex.parseScriptNum raw = some (Int.ofNat (2 + i.val)) ∧
          FirstOvershoot.fixedRegion[152 + i.val]? =
            some (hashes.h160 opening) := by
  unfold evalBare at accepted
  cases evaluated : evalScriptSig scriptSig with
  | none => simp [evaluated] at accepted
  | some stack =>
      have lockAccepted : run hashes ByteLayout.program
          (State.mk stack outcomes 0) = some final := by
        simpa [evaluated] using accepted
      obtain ⟨nonce, puzzle, raw, tail, later, shape, checks,
        i, opening, parsed, matched⟩ :=
        PinningShape.accepted_arbitrary_initial_stack_first_origin
          hashes stack outcomes final lockAccepted
      exact ⟨stack, by simp, nonce, puzzle, raw, tail, later,
        shape, checks, i, opening, parsed, matched⟩

/-- In one truthy modeled bare-script run, the first signed HORS comparison
uses a lock-owned commitment and the last multisignature has fixed 10-of-10
count operands with a true supplied outcome. Nothing here identifies the
intervening seven signed/two bonus final-round sources or proves Core
signature validity. -/
theorem accepted_bare_first_origin_and_final_counts {σ : Type*}
    (evalScriptSig : σ → Option (List Bytes)) (hashes : Hashes)
    (outcomes : List Bool) (scriptSig : σ) (final : State)
    (accepted : evalBare evalScriptSig hashes outcomes scriptSig = some final)
    (truth : finalTruth final = true) :
    ∃ stack, evalScriptSig scriptSig = some stack ∧
      (∃ nonce puzzle raw tail later,
        stack = nonce :: puzzle :: raw :: tail ∧
        outcomes = true :: true :: later ∧
        ∃ i : Fin 150, ∃ opening : Bytes,
          ByteIndex.parseScriptNum raw = some (Int.ofNat (2 + i.val)) ∧
          FirstOvershoot.fixedRegion[152 + i.val]? =
            some (hashes.h160 opening)) ∧
      (∃ beforeSuffix beforeCheck,
        run hashes (ByteLayout.program.take 857)
          (State.mk stack outcomes 0) = some beforeSuffix ∧
        run hashes ByteFinalCounts.finalSetup beforeSuffix = some beforeCheck ∧
        beforeCheck.stack[0]? = some [0x0a] ∧
        beforeCheck.stack[11]? = some [0x0a] ∧
        beforeCheck.outcomes.head? = some true) := by
  obtain ⟨stack, evaluated, nonce, puzzle, raw, tail, later,
    shape, checks, i, opening, parsed, matched⟩ :=
    accepted_bare_composition_first_origin evalScriptSig hashes outcomes
      scriptSig final accepted
  have lockAccepted : run hashes ByteLayout.program
      (State.mk stack outcomes 0) = some final := by
    simpa [evalBare, evaluated] using accepted
  obtain ⟨beforeSuffix, beforeCheck, prefixRun, setup,
    keyCount, sigCount, finalOutcome⟩ :=
    ByteFinalCounts.accepted_true_whole_program_final_counts
      hashes (State.mk stack outcomes 0) final lockAccepted truth
  exact ⟨stack, evaluated,
    ⟨nonce, puzzle, raw, tail, later, shape, checks,
      i, opening, parsed, matched⟩,
    ⟨beforeSuffix, beforeCheck, prefixRun, setup,
      keyCount, sigCount, finalOutcome⟩⟩

end QSB.BareBoundary
